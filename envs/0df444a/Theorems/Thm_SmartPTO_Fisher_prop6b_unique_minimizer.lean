-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop6b_unique_minimizer
-- name    : SmartPTO.Fisher.prop6b_unique_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:20.304095+00:00
-- url     : https://prove2.me/theorems/9affcc47-edfd-43db-be7c-aa2be23c222a
-- title:
--   Proposition 6(b) — uniqueness of the SPO+ risk minimizer
-- statement:
--   Let $P$ be an integrable probability law on $\mathbb R^d$, centrally symmetric about its mean $\bar c$ and continuous on all of $\mathbb R^d$. Let $S$ be nonempty, compact, convex, and have nonempty interior, with an arbitrary optimal-decision oracle $w^*$. If a prediction $\hat c$ has SPO+ risk no greater than that of $\bar c$, then
--
--   $$R_{\mathrm{SPO+}}(\hat c)\le R_{\mathrm{SPO+}}(\bar c)\quad\Longrightarrow\quad\hat c=\bar c.$$
--
--   Together with Proposition 6(a), this says the mean is the unique minimizer of the surrogate risk.
--
--   **Formalization Note** The risk is an extended nonnegative integral. “Continuous on all” is pinned to absolute continuity plus full support: an absolutely continuous law supported inside a small ball can have many minimizers, contrary to the printed uniqueness claim.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 23, Proposition 6(b); §4.1 p. 22

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 6(b), p. 23: under nonempty interior the mean is the unique minimizer. -/
theorem prop6b_unique_minimizer {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (hCont : ContinuousOnAll P)
    (hSymm : CentrallySymmetric P) (hSinner : (interior S).Nonempty)
    (chat : EuclideanSpace ℝ (Fin d))
    (hMin : spoPlusRisk S wstar P chat ≤ spoPlusRisk S wstar P (∫ c, c ∂P)) :
    chat = ∫ c, c ∂P := by sorry

end SmartPTO.Fisher
