-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_lemma_3_4_bayes_risk_via_inner_risk_v2
-- name    : SupportVectorMachines.Calibration.lemma_3_4_bayes_risk_via_inner_risk_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:00.938107+00:00
-- url     : https://prove2.me/theorems/cb886e8b-0490-4220-96e2-ec04114052f3
-- title:
--   Lemma 3.4 — the Bayes risk is the integral of the minimal inner risks (measurable loss)
-- statement:
--   This is Lemma 3.4 (Computation of Bayes risks) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 52), the bridge between the outer Bayes risk $R^*_{L,P}$ and the pointwise (inner) minimization apparatus of Chapter 3.
--
--   Let $X$ be a complete measurable space, $L : X \times Y \times \mathbb R \to [0,\infty)$ a loss (Definition 2.1: measurable and nonnegative), and $P$ a distribution on $X \times Y$, represented by $(P_X,\kappa)$ with $\kappa(x) = P(\cdot\mid x)$ a measurable family of conditional distributions. Then $x \mapsto C^*_{L,P(\cdot\mid x),x}$ is measurable, and
--   $$
--   R^*_{L,P} = \int_X C^*_{L,P(\cdot\mid x),x}\,dP_X(x).
--   $$
--
--   The Bayes risk — an infimum over all measurable functions on $X$ — is thus exactly the integral of a pointwise, one-real-variable minimization.
--
--   **Formalization Note.** The retired version quantified over the bare function type `X → ℝ → ℝ → ℝ`, so a loss depending non-measurably on $x$ made $x \mapsto C^*$ non-measurable (the accepted disproof). The corrected statement takes $L$ in the bundled `Loss X` (measurable and nonnegative, Definition 2.1's own requirements) and uses the book's definition of a complete measurable space. Conventions made explicit (common to the corrected Chapter 3 milestones): a loss is the bundled `Loss X` of Definition 2.1 — measurable on $X \times \mathbb R \times \mathbb R$ and nonnegative — with the closed label set $Y$ embedded in $\mathbb R$ (a loss on $X \times Y \times \mathbb R$ extends by $0$ outside $Y$, a distribution on $X \times Y$ is one on $X \times \mathbb R$ supported on $X \times Y$, and a set $\mathcal Q$ of distributions on $Y$ is a set of measures on $\mathbb R$); a distribution $P$ on $X \times Y$ is represented by its marginal $P_X$ (a probability measure) together with a measurable family $\kappa : X \to \mathcal M(\mathbb R)$ of probability measures, the regular conditional probabilities $P(\cdot\mid x)$ (which exist since $Y$ is Polish, Lemma A.3.16; every statement is invariant under the choice of version), so that risks are written in the form of Eq. (3.5); all risks are $[0,\infty]$-valued Lebesgue integrals, as in the book; and `IsCompleteMeasurableSpace` is now the book's own notion (the $\sigma$-algebra equals its universal completion) instead of the retired stronger sufficient condition.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 52, Lemma 3.4

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Lemma 3.4 (Computation of Bayes risks), Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, p. 52: let `X` be a complete measurable space, `L : X × Y × ℝ → [0,∞)` be a loss
(Definition 2.1: measurable and nonnegative, both bundled in `Loss X`), and `P` (represented by
`(PX, κ)`, `κ` a measurable family of conditional distributions `P(·|x)`) be a distribution on
`X × ℝ`. Then `x ↦ C*_{L,P(·|x),x}` is measurable and `R*_{L,P} = ∫_X C*_{L,P(·|x),x} dPX(x)`.
Corrected version of `lemma_3_4_bayes_risk_via_inner_risk`, whose `Loss X` was the bare function
type (no measurability), and whose completeness notion was a stronger sufficient condition. -/
theorem lemma_3_4_bayes_risk_via_inner_risk_v2 {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x)) :
    Measurable (fun x => minInnerRisk L (κ x) x) ∧
      bayesRisk L PX κ = ∫⁻ x, minInnerRisk L (κ x) x ∂PX := by sorry

end SupportVectorMachines.Calibration
