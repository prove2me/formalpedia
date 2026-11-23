-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_Supplement_theorem5_moreover
-- name    : StarShapedRisk.Representation.Supplement.theorem5_moreover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:48:36.584309+00:00
-- url     : https://prove2.me/theorems/af35f3d2-7765-4d7c-841c-768fcf2a8eab
-- title:
--   Theorem 5 (Moreover clause) — closure of law-invariant star-shaped risk measures
-- statement:
--   Fix an atomless probability space and the space $\mathcal X$ of bounded measurable losses. The class of star-shaped, law-invariant risk measures is closed under all four operations from Theorem 1:
--   $$\rho_\mu(X)=\int_I\rho_i(X)\,d\mu(i),\quad
--   \rho_\vee(X)=\sup_i\rho_i(X),\quad
--   \rho_\wedge(X)=\inf_i\rho_i(X),\quad
--   \rho_\square(X)=\inf_{\sum_iY_i=X}\sum_i\rho_i(Y_i).$$
--   For the average, $\mu$ is a probability on all subsets of $I$. For the supremum and infimum, $I$ is nonempty. The inf-convolution has $I=\{1,\ldots,n\}$, $n>0$, and condition (10), namely $\sum_i\rho_i(Z_i)\ge0$ for every zero-sum allocation. Each aggregate is a real-valued, normalized, translation-invariant, monotone, star-shaped and law-invariant risk measure. This is the entire Moreover clause, including the inf-convolution.
--
--   Differences from the source:
--   - encoding: L∞ positions and the four operations of Theorem 1 → published bounded measurable carrier packaged as PositionSpace, with all four closure assertions conjoined; reason: retain all operations on the existing carrier; the indicated invariance identifies almost-sure equal representatives
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2647, Theorem 5 (Moreover clause)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_Supplement_LawPositionSpace

namespace StarShapedRisk.Representation.Supplement

theorem theorem5_moreover {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (hP : StarShapedRisk.LawInvariant.IsAtomless P) :
    (∀ (I : Type*) [MeasurableSpace I] (hI : ‹MeasurableSpace I› = ⊤)
      (μ : MeasureTheory.Measure I) [MeasureTheory.IsProbabilityMeasure μ]
      (ρ : I → StarShapedRisk.LawInvariant.Positions Ω → ℝ),
      (∀ i, (StarShapedRisk.LawInvariant.IsRiskMeasure (ρ i) ∧ StarShapedRisk.LawInvariant.IsStarShaped (ρ i) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (ρ i))) →
      (StarShapedRisk.LawInvariant.IsRiskMeasure (riskAverage (lawPositionSpace Ω) μ ρ) ∧ StarShapedRisk.LawInvariant.IsStarShaped (riskAverage (lawPositionSpace Ω) μ ρ) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (riskAverage (lawPositionSpace Ω) μ ρ))) ∧
    (∀ (I : Type*) [Nonempty I] (ρ : I → StarShapedRisk.LawInvariant.Positions Ω → ℝ),
      (∀ i, (StarShapedRisk.LawInvariant.IsRiskMeasure (ρ i) ∧ StarShapedRisk.LawInvariant.IsStarShaped (ρ i) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (ρ i))) →
      (StarShapedRisk.LawInvariant.IsRiskMeasure (riskSup (lawPositionSpace Ω) ρ) ∧ StarShapedRisk.LawInvariant.IsStarShaped (riskSup (lawPositionSpace Ω) ρ) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (riskSup (lawPositionSpace Ω) ρ))) ∧
    (∀ (I : Type*) [Nonempty I] (ρ : I → StarShapedRisk.LawInvariant.Positions Ω → ℝ),
      (∀ i, (StarShapedRisk.LawInvariant.IsRiskMeasure (ρ i) ∧ StarShapedRisk.LawInvariant.IsStarShaped (ρ i) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (ρ i))) →
      (StarShapedRisk.LawInvariant.IsRiskMeasure (riskInf (lawPositionSpace Ω) ρ) ∧ StarShapedRisk.LawInvariant.IsStarShaped (riskInf (lawPositionSpace Ω) ρ) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (riskInf (lawPositionSpace Ω) ρ))) ∧
    (∀ (n : ℕ), 0 < n → ∀ (ρ : Fin n → StarShapedRisk.LawInvariant.Positions Ω → ℝ),
      (∀ i, (StarShapedRisk.LawInvariant.IsRiskMeasure (ρ i) ∧ StarShapedRisk.LawInvariant.IsStarShaped (ρ i) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (ρ i))) → NormalityCondition (lawPositionSpace Ω) ρ →
      (StarShapedRisk.LawInvariant.IsRiskMeasure (infConvolution (lawPositionSpace Ω) ρ) ∧ StarShapedRisk.LawInvariant.IsStarShaped (infConvolution (lawPositionSpace Ω) ρ) ∧ StarShapedRisk.LawInvariant.IsLawInvariant P (infConvolution (lawPositionSpace Ω) ρ))) := by sorry

end StarShapedRisk.Representation.Supplement
