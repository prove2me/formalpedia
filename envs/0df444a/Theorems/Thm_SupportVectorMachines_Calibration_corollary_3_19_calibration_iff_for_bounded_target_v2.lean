-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_corollary_3_19_calibration_iff_for_bounded_target_v2
-- name    : SupportVectorMachines.Calibration.corollary_3_19_calibration_iff_for_bounded_target_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:16.026364+00:00
-- url     : https://prove2.me/theorems/cc1901be-215b-44a3-bb31-aa5cbf537180
-- title:
--   Corollary 3.19 — calibration is equivalent to a uniform risk implication when the target loss is bounded (measurable losses)
-- statement:
--   This is Corollary 3.19 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 63), the mission's goal.
--
--   Let $X$ be a complete measurable space, $L_{\mathrm{tar}}, L_{\mathrm{sur}}$ losses (Definition 2.1: measurable and nonnegative), and $\mathcal Q$ a set of distributions on the label space. If $L_{\mathrm{tar}}$ is bounded (there is $B \in \mathbb R$ with $L_{\mathrm{tar}}(x,y,t) \le B$ for all $x,y,t$), then the following are equivalent:
--
--   1. $L_{\mathrm{sur}}$ is $L_{\mathrm{tar}}$-calibrated with respect to $\mathcal Q$;
--   2. for every $\varepsilon \in (0,\infty]$ and every distribution $P$ on $X \times Y$ of type $\mathcal Q$ with $R^*_{L_{\mathrm{sur}},P} < \infty$, there is $\delta \in (0,\infty]$ such that for every measurable $f : X \to \mathbb R$, $R_{L_{\mathrm{sur}},P}(f) < R^*_{L_{\mathrm{sur}},P} + \delta \implies R_{L_{\mathrm{tar}},P}(f) < R^*_{L_{\mathrm{tar}},P} + \varepsilon$.
--
--   Both the classification loss and the density-level-detection loss are bounded, so any calibrated surrogate is a reasonable surrogate in this asymptotic, uniform-over-$\mathcal Q$ sense.
--
--   **Formalization Note.** The retired version quantified over the bare function type for the losses: a target loss failing calibration at a point that no measure sees, on a trivial $\sigma$-algebra, satisfied (ii) because the lower integral of a non-measurable integrand only sees the best fibre. The corrected statement takes both losses in the bundled `Loss X` (measurable and nonnegative), uses the book's definition of a complete measurable space, and drops the retired extra hypothesis $B > 0$ ("bounded" only asks for some real bound; $L_{\mathrm{tar}} \equiv 0$ is bounded). Conventions made explicit (common to the corrected Chapter 3 milestones): a loss is the bundled `Loss X` of Definition 2.1 — measurable on $X \times \mathbb R \times \mathbb R$ and nonnegative — with the closed label set $Y$ embedded in $\mathbb R$ (a loss on $X \times Y \times \mathbb R$ extends by $0$ outside $Y$, a distribution on $X \times Y$ is one on $X \times \mathbb R$ supported on $X \times Y$, and a set $\mathcal Q$ of distributions on $Y$ is a set of measures on $\mathbb R$); a distribution $P$ on $X \times Y$ is represented by its marginal $P_X$ (a probability measure) together with a measurable family $\kappa : X \to \mathcal M(\mathbb R)$ of probability measures, the regular conditional probabilities $P(\cdot\mid x)$ (which exist since $Y$ is Polish, Lemma A.3.16; every statement is invariant under the choice of version), so that risks are written in the form of Eq. (3.5); all risks are $[0,\infty]$-valued Lebesgue integrals, as in the book; and `IsCompleteMeasurableSpace` is now the book's own notion (the $\sigma$-algebra equals its universal completion) instead of the retired stronger sufficient condition.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 63, Corollary 3.19

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction_v2
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Corollary 3.19, Steinwart & Christmann, *Support Vector Machines*, Springer 2008, p. 63: let
`X` be a complete measurable space, `Ltar, Lsur` be two losses (Definition 2.1: measurable and
nonnegative, bundled in `Loss X`), and `𝒬` be a set of distributions on `Y`. If `Ltar` is bounded
(`∀ x y t, Ltar x y t ≤ B` for some real `B`), then the following are equivalent: i) `Lsur` is
`Ltar`-calibrated with respect to `𝒬`. ii) for all `ε ∈ (0,∞]` and all distributions `P` of type
`𝒬` with `R*_{Lsur,P} < ∞`, there exists `δ ∈ (0,∞]` such that for all measurable `f : X → ℝ`,
`R_{Lsur,P}(f) < R*_{Lsur,P} + δ` implies `R_{Ltar,P}(f) < R*_{Ltar,P} + ε`.
Corrected version of `corollary_3_19_calibration_iff_for_bounded_target`, whose `Loss X` was the
bare function type (no measurability, so a non-measurable target loss broke the equivalence),
whose completeness notion was a stronger sufficient condition, and which required `0 < B`
(excluding the bounded loss `Ltar ≡ 0`). -/
theorem corollary_3_19_calibration_iff_for_bounded_target_v2 {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ))
    (B : ℝ) (hBdd : ∀ x y t, Ltar x y t ≤ B) :
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
