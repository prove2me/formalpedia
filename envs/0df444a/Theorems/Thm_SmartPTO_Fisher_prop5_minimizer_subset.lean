-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop5_minimizer_subset
-- name    : SmartPTO.Fisher.prop5_minimizer_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:28.345985+00:00
-- url     : https://prove2.me/theorems/fa64443c-126f-4664-ab4c-dcb9b1747ff1
-- title:
--   Proposition 5, first sentence — SPO risk minimizers select mean-optimal decisions
-- statement:
--   Let $P$ be an integrable probability law on $\mathbb R^d$, with mean $\bar c=\mathbb E_P[c]$, and let $S$ be a nonempty compact convex feasible set. If a cost prediction $c^*$ minimizes the true SPO risk over all predictions, then
--
--   $$W^*(c^*)\subseteq W^*(\bar c).$$
--
--   Every decision optimal for the prediction is then also optimal for the mean cost.
--
--   **Formalization Note** The SPO loss is Definition 2's maximum over all prediction-optimal decisions, and its risk is an extended nonnegative integral. No continuity or symmetry condition is added.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 22, Proposition 5, first sentence; §4.1 p. 22

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 5, first sentence, p. 22. -/
theorem prop5_minimizer_subset {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (cstar : EuclideanSpace ℝ (Fin d))
    (hMin : ∀ chat : EuclideanSpace ℝ (Fin d), spoRisk S P cstar ≤ spoRisk S P chat) :
    Wstar S cstar ⊆ Wstar S (∫ c, c ∂P) := by sorry

end SmartPTO.Fisher
