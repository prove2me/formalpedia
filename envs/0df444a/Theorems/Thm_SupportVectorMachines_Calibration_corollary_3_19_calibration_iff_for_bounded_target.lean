-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_corollary_3_19_calibration_iff_for_bounded_target
-- name    : SupportVectorMachines.Calibration.corollary_3_19_calibration_iff_for_bounded_target
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:11.256698+00:00
-- url     : https://prove2.me/theorems/89589f2d-9272-4e8a-8881-ac070944f5d9
-- title:
--   Corollary 3.19 — calibration is equivalent to a uniform risk implication when the target loss is bounded
-- statement:
--   This is Corollary 3.19 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 63), the mission's goal: the positive counterpart to Theorem 3.17, showing that for a
--   bounded target loss, calibration is not just necessary but *sufficient* for the risk
--   implication of Question 3.1, uniformly over a whole class $\mathcal Q$ of label
--   distributions.
--
--   Let $X$ be a complete measurable space, $L_{\mathrm{tar}}, L_{\mathrm{sur}}$ be losses, and
--   $\mathcal Q$ a set of distributions on the label space. If $L_{\mathrm{tar}}$ is bounded
--   (there is $B > 0$ with $L_{\mathrm{tar}}(x,y,t) \le B$ for all $x,y,t$), then the following
--   are equivalent:
--
--   1. $L_{\mathrm{sur}}$ is $L_{\mathrm{tar}}$-calibrated with respect to $\mathcal Q$.
--   2. For every $\varepsilon \in (0,\infty]$ and every distribution $P$ of type $\mathcal Q$
--      with $R^*_{L_{\mathrm{sur}},P} < \infty$, there exists $\delta \in (0,\infty]$ such that,
--      for every measurable $f : X \to \mathbb R$, $R_{L_{\mathrm{sur}},P}(f) <
--      R^*_{L_{\mathrm{sur}},P} + \delta \implies R_{L_{\mathrm{tar}},P}(f) <
--      R^*_{L_{\mathrm{tar}},P} + \varepsilon$.
--
--   Both the classification loss and the density-level-detection loss are bounded, so this
--   corollary certifies that any calibrated surrogate (e.g. the hinge or least-squares loss for
--   classification, by Example 3.16) is automatically a reasonable surrogate in this
--   asymptotic, uniform-over-$\mathcal Q$ sense — the qualitative justification for using such
--   surrogates at all, ahead of the sharper *quantitative* relationships (Zhang's inequality,
--   Theorem 2.31, and Theorem 3.22) the book develops afterward.
--
--   **Formalization Note** `∀ x, IsProbabilityMeasure (κ x)` is added to the inner
--   "distribution $P$ of type $\mathcal Q$" quantifier, for the same reason as in Theorem 3.17
--   and Lemma 3.4: `IsOfType`/`outerRisk`/`bayesRisk` do not force $\kappa(x)$ to be a probability
--   measure by their types, but the book's "$P$ a distribution on $X \times Y$" does require it.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 63, Corollary 3.19

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Corollary 3.19, p. 63: let `X` be a complete measurable space, `Ltar, Lsur` be two losses,
and `𝒬` be a set of distributions on `Y`. If `Ltar` is bounded (`∃ B > 0, ∀ x y t,
Ltar x y t ≤ B`), then the following are equivalent: i) `Lsur` is `Ltar`-calibrated with
respect to `𝒬`. ii) for all `ε ∈ (0,∞]` and all distributions `P` of type `𝒬` with
`R*_{Lsur,P} < ∞`, there exists `δ ∈ (0,∞]` such that for all measurable `f : X → ℝ`,
`R_{Lsur,P}(f) < R*_{Lsur,P} + δ` implies `R_{Ltar,P}(f) < R*_{Ltar,P} + ε`. -/
theorem corollary_3_19_calibration_iff_for_bounded_target {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ))
    (B : ℝ) (hB : 0 < B) (hBdd : ∀ x y t, Ltar x y t ≤ B) :
    IsCalibrated Ltar Lsur 𝒬 ↔
      ∀ ε : ENNReal, 0 < ε →
        ∀ (PX : Measure X) (κ : X → Measure ℝ), Measurable κ → IsProbabilityMeasure PX →
          (∀ x, IsProbabilityMeasure (κ x)) →
          IsOfType κ PX 𝒬 → bayesRisk Lsur PX κ < ⊤ →
          ∃ δ : ENNReal, 0 < δ ∧
            ∀ f : X → ℝ, Measurable f →
              outerRisk Lsur PX κ f < bayesRisk Lsur PX κ + δ →
              outerRisk Ltar PX κ f < bayesRisk Ltar PX κ + ε := by sorry

end SupportVectorMachines.Calibration
