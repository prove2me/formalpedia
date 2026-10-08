-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_corollary_4
-- name    : SelfDualLP.Regularity.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:14.53099+00:00
-- url     : https://prove2.me/theorems/c735bade-09ae-4172-ba22-8d115ad85bf5
-- title:
--   Corollary 4: positive κ at an HLP optimum detects infeasibility
-- statement:
--   Use the paper's choice $y^0=0$ and $x^0=s^0=e$. Let $(y,x,\tau,\theta,s,\kappa)$ be any optimal solution of (HLP). If $\kappa>0$, then
--   $$
--   \text{(LP) is infeasible}\quad\text{or}\quad\text{(LD) is infeasible}.
--   $$
--   The disjunction is inclusive. Theorem 2(iv) supplies $\theta=0$ at an optimal solution; it is not an additional assumption here.
--
--   This result distinguishes certificates of infeasibility from the case in which both original programs have feasible points.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 59, Corollary 4; DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_HLP

namespace SelfDualLP.Regularity

/-- Ye--Todd--Mizuno (1994), Corollary 4, p. 59. -/
theorem corollary_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n)
    (hw : IsSelfComplementary A b c w) (hκ : 0 < w.κ) :
    (¬ ∃ x, PrimalFeasible A b c x) ∨
      (¬ ∃ y, DualFeasible A c y) := by sorry

end SelfDualLP.Regularity
