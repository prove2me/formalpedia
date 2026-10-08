-- Prove2me | Theorems.Thm_RobustUncLP_Ellipsoidal_robustFeas_iff_P_nonneg
-- name    : RobustUncLP.Ellipsoidal.robustFeas_iff_P_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:51.936106+00:00
-- url     : https://prove2.me/theorems/8aeee7b8-ab5b-4876-9b8e-28b69ad42b34
-- title:
--   Appendix, (I), p. 15 — x with fᵀx = 1 is robust feasible iff every (P_i[x]) has nonnegative optimal value
-- statement:
--   Let $\mathcal U$ be given by the data of (15) and let $x \in \mathbb R^n$ satisfy $f^Tx = 1$. Then $x$ is robust feasible for $\mathcal U$ if and only if, for every row $i = 1, \dots, m$, the objective of $(P_i[x])$ is nonnegative on the whole feasible set of $(P_i[x])$:
--   $$x \in G_{\mathcal U} \iff \forall i,\ \forall (u^0,\dots,u^k) \text{ feasible for } (P_i[x]):\ \ a_i[\Pi_0(u^0)]^Tx \ge 0.$$
--
--   This is claim (I) of the Appendix: robust feasibility is the nonnegativity of $m$ optimal values. Conic duality then turns each into the system $(\mathcal C_i)$.
--
--   **Formalization Note** "The optimal value is nonnegative" is stated as "every feasible value is nonnegative". The two are the same, including when $(P_i[x])$ is infeasible (optimal value $+\infty$), and this form avoids an infimum over a possibly empty set. No condition B or C is needed.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, Appendix, p. 15, claim (I) and (P_i[x])

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

namespace RobustUncLP.Ellipsoidal

open Matrix EllipsoidalData

/-- Appendix, claim (I), p. 15: a point `x` with `fᵀx = 1` is robust feasible iff, for every row
`i`, the objective `a_i[Π_0(u⁰)]ᵀx` of `(P_i[x])` is nonnegative on its whole feasible set. -/
theorem robustFeas_iff_P_nonneg {m n k : ℕ} (D : EllipsoidalData m n k) (f : Fin n → ℝ)
    (x : Fin n → ℝ) (hfx : f ⬝ᵥ x = 1) :
    x ∈ RobustUncLP.WorstCase.robustFeas D.uncSet f ↔ ∀ i : Fin m, ∀ u ∈ PFeas D, 0 ≤ (D.Pi 0 (u 0) *ᵥ x) i := by sorry

end RobustUncLP.Ellipsoidal
