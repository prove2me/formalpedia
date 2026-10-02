-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_lemma_3_4_bayes_risk_via_inner_risk
-- name    : SupportVectorMachines.Calibration.lemma_3_4_bayes_risk_via_inner_risk
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:29:21.63139+00:00
-- url     : https://prove2.me/theorems/c907d52c-f629-4dfc-a85c-9cc90bd85198
-- title:
--   Lemma 3.4 — the Bayes risk is the integral of the minimal inner risks
-- statement:
--   This is Lemma 3.4 (Computation of Bayes risks) of Steinwart & Christmann, *Support Vector
--   Machines* (Springer 2008, p. 52), the foundational bridge between the outer Bayes risk
--   $R^*_{L,P}$ and the pointwise (inner) minimization apparatus this chapter builds.
--
--   Let $X$ be a complete measurable space, $L$ a loss, and $P$ a distribution on $X \times Y$
--   (represented by $(P_X, \kappa)$, $\kappa$ a measurable family of conditional distributions
--   $P(\cdot \mid x)$). Then $x \mapsto C^*_{L,P(\cdot\mid x),x}$ is measurable, and
--   $$
--   R^*_{L,P} = \int_X C^*_{L,P(\cdot\mid x),x} \, dP_X(x).
--   $$
--
--   The result shows the Bayes risk — an infimum over all measurable functions on $X$, a priori
--   an infinite-dimensional optimization — is exactly the integral of a pointwise (one-real-
--   variable) minimization, which is what makes the inner-risk apparatus of this chapter useful
--   at all.
--
--   **Formalization Note** `κ x` is required to be a probability measure for every $x$ (matching
--   "$P(\cdot\mid x)$ a conditional distribution on $Y$"), a hypothesis added explicitly since
--   `bayesRisk`/`innerRisk` do not force this by their types.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 52, Lemma 3.4

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Lemma 3.4 (Computation of Bayes risks), p. 52: let `X` be a complete measurable space,
`L : X × Y × ℝ → [0,∞)` be a loss, and `P` (represented by `(PX, κ)`, `κ` a measurable family of
conditional distributions `P(·|x)`) be a distribution on `X × ℝ`. Then `x ↦ C*_{L,P(·|x),x}` is
measurable and `R*_{L,P} = ∫_X C*_{L,P(·|x),x} dPX(x)`. -/
theorem lemma_3_4_bayes_risk_via_inner_risk {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x)) :
    Measurable (fun x => minInnerRisk L (κ x) x) ∧
      bayesRisk L PX κ = ∫⁻ x, minInnerRisk L (κ x) x ∂PX := by sorry

end SupportVectorMachines.Calibration
