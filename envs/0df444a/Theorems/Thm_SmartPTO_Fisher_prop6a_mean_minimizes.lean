-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop6a_mean_minimizes
-- name    : SmartPTO.Fisher.prop6a_mean_minimizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:10.469985+00:00
-- url     : https://prove2.me/theorems/1a2d3b21-75e7-4046-a0b8-dd3f29984e51
-- title:
--   Proposition 6(a) — the mean minimizes the SPO+ risk
-- statement:
--   Let $P$ be an integrable probability law on cost vectors in $\mathbb R^d$, with mean $\bar c=\mathbb E_P[c]$. Let $S$ be nonempty, compact, and convex, and let $w^*$ be an optimal-decision oracle. Suppose $P$ is continuous on all of $\mathbb R^d$ and centrally symmetric about $\bar c$. Then, for every prediction $\hat c$,
--
--   $$R_{\mathrm{SPO+}}(\bar c)\le R_{\mathrm{SPO+}}(\hat c).$$
--
--   The mean is therefore a population minimizer of the surrogate risk.
--
--   **Formalization Note** “Continuous on all” means absolute continuity and full support. The latter is retained here because it is part of the paper's common premise for both parts of Proposition 6. Risk takes values in $[0,\infty]$; integrability of costs gives the finite-mean convention of §4.1.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 23, Proposition 6(a); §4.1 p. 22

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 6(a), p. 23: the mean minimizes SPO+ risk. -/
theorem prop6a_mean_minimizes {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (hCont : ContinuousOnAll P)
    (hSymm : CentrallySymmetric P)
    (chat : EuclideanSpace ℝ (Fin d)) :
    spoPlusRisk S wstar P (∫ c, c ∂P) ≤ spoPlusRisk S wstar P chat := by sorry

end SmartPTO.Fisher
