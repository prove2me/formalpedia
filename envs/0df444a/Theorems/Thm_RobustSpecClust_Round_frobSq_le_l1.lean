-- Prove2me | Theorems.Thm_RobustSpecClust_Round_frobSq_le_l1
-- name    : RobustSpecClust.Round.frobSq_le_l1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:23.550512+00:00
-- url     : https://prove2.me/theorems/8aa20e0a-ff51-41e0-aad6-e958f3ec01de
-- title:
--   (G.6)(iii), p. 46 — for A, B with entries in [0,1], ‖A − B‖²_F ≤ ‖A − B‖₁
-- statement:
--   Let $A, B \in \mathbb R^{n\times n}$ have all entries in $[0,1]$. Then the squared Frobenius norm of their difference is at most its entrywise $\ell_1$ norm:
--   $$\|A - B\|_F^2 = \sum_{i,j}(A_{ij}-B_{ij})^2 \;\le\; \sum_{i,j}|A_{ij}-B_{ij}| = \|A - B\|_1 .$$
--
--   Applied to $A = \hat X$ and $B = X^0$, this is step (iii) of (G.6), which turns the Davis–Kahan bound into a bound in terms of the $\ell_1$ estimation error that Theorem 1 controls.
-- source:
--   arXiv:1912.07546v3, Appendix G, proof of Theorem 2, p. 46, (G.6)(iii)

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

theorem frobSq_le_l1 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) (hB : ∀ i j, 0 ≤ B i j ∧ B i j ≤ 1) :
    frobSq (A - B) ≤ l1 (A - B) := by sorry

end RobustSpecClust.Round
