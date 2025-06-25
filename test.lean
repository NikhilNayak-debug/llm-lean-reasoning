-- Lean 4 or Lean 3
import Mathlib.Data.Real.Basic

example (a b : ℝ) (h : a^2 + b^2 = 2) : a * b ≤ 1 := by
  have h1 : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
  have : a^2 + b^2 - 2*a*b ≥ 0 := by
    rw ←sub_nonneg
    rw ←sq_sub_sq
    exact h1
  linarith [h]
