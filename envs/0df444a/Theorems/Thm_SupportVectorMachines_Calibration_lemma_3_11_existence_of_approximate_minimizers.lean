-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_lemma_3_11_existence_of_approximate_minimizers
-- name    : SupportVectorMachines.Calibration.lemma_3_11_existence_of_approximate_minimizers
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:25.641055+00:00
-- url     : https://prove2.me/theorems/742131c3-3223-4c05-b47a-c71a43879490
-- title:
--   Lemma 3.11 — finiteness of the minimal inner risk characterizes existence of approximate minimizers
-- statement:
--   This is Lemma 3.11 (Existence of approximate minimizers) of Steinwart & Christmann, *Support
--   Vector Machines* (Springer 2008, p. 57), directly cited in the proof of Theorem 3.17
--   ("Furthermore, by Lemma 3.11, we find measurable functions...").
--
--   Let $X$ be a complete measurable space, $L$ a loss, $P$ a distribution on $X \times Y$
--   (represented by $(P_X,\kappa)$ as above), and $\varepsilon \in (0,\infty]$. Then the
--   following are equivalent:
--
--   1. $C^*_{L,P(\cdot\mid x),x} < \infty$ for $P_X$-almost all $x \in X$.
--   2. There exists a measurable $f : X \to \mathbb R$ such that $f(x) \in
--      M_{L,P(\cdot\mid x),x}(\varepsilon)$ for $P_X$-almost all $x \in X$.
--
--   The lemma isolates exactly when a uniform choice of approximate minimizer can be made
--   measurably: pointwise finiteness of the minimal inner risk (an a.e. condition, easy to check)
--   is equivalent to the existence of a genuine measurable selection.
--
--   **Formalization Note** As in Lemma 3.4, `∀ x, IsProbabilityMeasure (κ x)` is added
--   explicitly. "$P_X$-almost all $x$" is `∀ᵐ x ∂PX, ...`, Mathlib's a.e.-filter idiom.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 57, Lemma 3.11

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Lemma 3.11 (Existence of approximate minimizers), p. 57: let `X` be a complete measurable
space, `L : X × Y × ℝ → [0,∞)` be a loss, `P` (represented by `(PX, κ)`, `κ` a measurable family
of conditional distributions `P(·|x)`) be a distribution on `X × ℝ`, and `ε ∈ (0,∞]`. Then the
following are equivalent: i) `C*_{L,P(·|x),x} < ∞` for `PX`-almost all `x ∈ X`; ii) there exists
a measurable `f : X → ℝ` such that `f(x) ∈ M_{L,P(·|x),x}(ε)` for `PX`-almost all `x ∈ X`. -/
theorem lemma_3_11_existence_of_approximate_minimizers {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x))
    (ε : ENNReal) (hε : 0 < ε) :
    (∀ᵐ x ∂PX, minInnerRisk L (κ x) x < ⊤) ↔
      ∃ f : X → ℝ, Measurable f ∧ ∀ᵐ x ∂PX, f x ∈ approxMinimizers L (κ x) x ε := by sorry

end SupportVectorMachines.Calibration
