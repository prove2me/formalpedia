-- Prove2me | Theorems.Thm_SmartPTO_Fisher_prop5_converse
-- name    : SmartPTO.Fisher.prop5_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:31.205293+00:00
-- url     : https://prove2.me/theorems/568c449b-f14b-435b-a92b-5b587a842033
-- title:
--   Proposition 5, second sentence — a unique mean-optimal decision minimizes SPO risk
-- statement:
--   Let $P$ be an integrable probability law on $\mathbb R^d$, with mean $\bar c=\mathbb E_P[c]$, and let $S$ be a nonempty compact convex feasible set. Suppose the prediction $c^*$ has a singleton optimal-decision set $W^*(c^*)$ and that this set is contained in $W^*(\bar c)$. Then, for every prediction $\hat c$,
--
--   $$R_{\mathrm{SPO}}(c^*)\le R_{\mathrm{SPO}}(\hat c).$$
--
--   Thus a prediction whose unique selected decision optimizes mean cost minimizes the true SPO risk.
--
--   **Formalization Note** This uses the unambiguous loss of Definition 2 and imposes no symmetry or continuity on $P$.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 22, Proposition 5, second sentence; §4.1 p. 22

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Proposition 5, second sentence, p. 22. -/
theorem prop5_converse {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hInt : Integrable id P) (cstar : EuclideanSpace ℝ (Fin d))
    (hSingle : ∃ w, Wstar S cstar = {w})
    (hSub : Wstar S cstar ⊆ Wstar S (∫ c, c ∂P)) :
    ∀ chat : EuclideanSpace ℝ (Fin d), spoRisk S P cstar ≤ spoRisk S P chat := by sorry

end SmartPTO.Fisher
