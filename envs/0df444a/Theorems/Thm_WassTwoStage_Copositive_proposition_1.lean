-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_proposition_1
-- name    : WassTwoStage.Copositive.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:58:55.225292+00:00
-- url     : https://prove2.me/theorems/30e997f0-0b10-4fc7-a5cc-f3d19aa15353
-- title:
--   Proposition 1 — weak duality between the copositive program (24) and the completely positive program (25)
-- statement:
--   For every first-stage decision $x$ and every $\delta \ge 0$, the optimal value of the completely positive program (25) does not exceed that of the copositive program (24):
--   $$\underline{\mathcal Z}_\delta(x) \le \overline{\mathcal Z}_\delta(x).$$
--   In particular ($\delta = 0$), $\underline{\mathcal Z}(x) \le \overline{\mathcal Z}(x)$ for the programs (14) and (10).
--
--   The paper's Proposition 1 asserts that (14) is the conic dual of (10), "by standard conic duality theory". This statement formalizes the checkable consequence of that duality, weak duality, which is the part used later: in Theorem 5(iii), where (25) is a relaxation of (10), and in the comparison $\mathcal Z = \underline{\mathcal Z} \le \overline{\mathcal Z}$ of §3.3.
--
--   **Formalization Note** No standing assumption is needed for weak duality, so none is imposed. The $\delta$-perturbed version (24)/(25) of p. 17 contains Proposition 1 as the case $\delta = 0$. Values are in `EReal` (infeasible copositive program: $+\infty$; infeasible completely positive program: $-\infty$).
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 10, Proposition 1, (14); p. 17, (24), (25)

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

namespace WassTwoStage.Copositive

/-- Proposition 1, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 10, weak-duality content: the
copositive program (10) is dual to the completely positive program (14); in the
`δ`-perturbed form (24)/(25) of p. 17, every feasible value of the completely positive program
is at most every feasible value of the copositive program, i.e. `𝒵̲_δ(x) ≤ 𝒵̄_δ(x)` for every
`δ ≥ 0`. The case `δ = 0` is (14) versus (10). -/
theorem proposition_1 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    d.lowerValue δ x ≤ d.upperValue δ x := by sorry

end WassTwoStage.Copositive
