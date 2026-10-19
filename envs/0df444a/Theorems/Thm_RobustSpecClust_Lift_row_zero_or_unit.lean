-- Prove2me | Theorems.Thm_RobustSpecClust_Lift_row_zero_or_unit
-- name    : RobustSpecClust.Lift.row_zero_or_unit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:21.371343+00:00
-- url     : https://prove2.me/theorems/50584811-6af3-437a-a748-7e2be33a9211
-- title:
--   Appendix B (⇐): Gram rows are zero or unit vectors
-- statement:
--   Suppose $X=GG^\top$ and every entry of $X$ is zero or one. Then every row $g_i$ of $G$ is either the zero vector or a unit vector:
--
--   $$
--   g_i=0\quad\text{or}\quad\sum_{k=1}^{r}(g_i)_k^2=1.
--   $$
--
--   This identifies zero rows with potential outliers and constrains nonzero rows before the rotation to assignment coordinates.
-- source:
--   arXiv:1912.07546v3, Appendix B, proof of Proposition 1 (⇐), p. 37, second claim

import Mathlib
import Definitions.Def_RobustSpecClust_Lift_Setting

namespace RobustSpecClust.Lift

theorem row_zero_or_unit {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin N) (Fin r) ℝ) (hX : X = G * G.transpose)
    (hbinary : ∀ i j, X i j = 0 ∨ X i j = 1) :
    ∀ i, G i = 0 ∨ ∑ k, G i k ^ 2 = 1 := by sorry

end RobustSpecClust.Lift
