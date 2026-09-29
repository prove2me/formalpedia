-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_2_31_instance_zhang
-- name    : SupportVectorMachines.Classification.theorem_2_31_instance_zhang
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:22.121986+00:00
-- url     : https://prove2.me/theorems/932c0f52-4eec-4aee-8fda-58052b8c93ba
-- title:
--   Theorem 2.31 instance — excess classification risk bounded by excess hinge risk
-- statement:
--   This is the instance of Theorem 2.31 (Zhang's inequality) of Steinwart & Christmann, *Support
--   Vector Machines* (Springer 2008, p. 37), exactly as invoked in the proof of Theorem 8.1
--   ("we obtain by Theorem 2.31 that $R_{L_{\mathrm{class}},P}(f_{D,\lambda}) - R^*_{L_{\mathrm{class}},P}
--   \le R_{L,P}(f_{D,\lambda}) - R^*_{L,P,H}$" — the second inequality after substituting
--   $R^*_{L,P,H} = R^*_{L,P}$ from the Theorem 5.31 instance above).
--
--   For every measurable $f : X \to \mathbb R$ with finite hinge and classification risk,
--   $$
--   R_{L_{\mathrm{class}},P}(f) - R^*_{L_{\mathrm{class}},P} \le R_{L_{\mathrm{hinge}},P}(f) - R^*_{L_{\mathrm{hinge}},P}.
--   $$
--
--   This is exactly the second assertion of this series' `01-loss-functions` mission's
--   `zhang_inequality` (its full statement, including the first assertion's exact equality and
--   the general proof), restated locally here per Hard Rule 9 since a draft cannot import
--   another draft's items; `01-loss-functions` should be cited in the platform description as
--   the fuller treatment of this same result rather than re-derived.
--
--   **Formalization Note** Only the inequality (second) clause is restated, since it is the only
--   one Theorem 8.1's proof uses; the exact-equality first clause (which additionally needs
--   `f`-valued-in-`[-1,1]`) is out of scope for this instance.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 37, Theorem 2.31 (Zhang's inequality, second assertion, instantiated as in the proof of Theorem 8.1, p. 289); full statement and proof in this series' 01-loss-functions mission

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The instance of Theorem 2.31 (Zhang's inequality), p. 37, used inside the proof of Theorem
8.1: for every measurable `f : X → ℝ` with finite hinge and classification risk, the excess
classification risk is bounded by the excess (unrestricted) hinge risk,
`R_{L_class,P}(f) - R*_{L_class,P} ≤ R_{L_hinge,P}(f) - R*_{L_hinge,P}`. This is the chapter's own
formalization series's `01-loss-functions` mission's `zhang_inequality`, second clause, restated
locally per Hard Rule 9 rather than imported. -/
theorem theorem_2_31_instance_zhang {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (f : X → ℝ) (hf : Measurable f)
    (hInt1 : Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P)
    (hInt2 : Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P) :
    risk classLoss P f - bayesRisk classLoss P ≤
      risk hingeLoss P f - bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.Classification
