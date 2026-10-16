-- Prove2me | Theorems.Thm_RobustSpecClust_Lift_rows_eq_or_orthogonal
-- name    : RobustSpecClust.Lift.rows_eq_or_orthogonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:25.017526+00:00
-- url     : https://prove2.me/theorems/d95b1692-2489-4bb3-93a8-172a67258bae
-- title:
--   Appendix B (⇐): distinct nonzero Gram rows are orthogonal
-- statement:
--   Suppose $X=GG^\top$ and every entry of $X$ is zero or one. Any two nonzero rows $g_i,g_j$ of $G$ are either equal or orthogonal:
--
--   $$
--   g_i=g_j\quad\text{or}\quad\sum_{k=1}^{r}(g_i)_k(g_j)_k=0.
--   $$
--
--   Thus the distinct nonzero rows give mutually orthogonal cluster directions. This combines the proof's basis-orthogonality and row-exhaustion claims without fixing its proof-local basis.
-- source:
--   arXiv:1912.07546v3, Appendix B, proof of Proposition 1 (⇐), pp. 37–38, orthonormal-basis and row-exhaustion claims

import Mathlib
import Definitions.Def_RobustSpecClust_Lift_Setting

namespace RobustSpecClust.Lift

theorem rows_eq_or_orthogonal {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin N) (Fin r) ℝ) (hX : X = G * G.transpose)
    (hbinary : ∀ i j, X i j = 0 ∨ X i j = 1) :
    ∀ i j, G i ≠ 0 → G j ≠ 0 → G i = G j ∨ ∑ k, G i k * G j k = 0 := by sorry

end RobustSpecClust.Lift
