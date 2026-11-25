-- Prove2me | Theorems.Thm_PI_AprimeInfG_tubeChart_of
-- name    : PI.AprimeInfG.tubeChart_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:38.821888+00:00
-- url     : https://prove2.me/theorems/14d7efe8-2019-45b9-bfd2-fd270aee5ad3
-- title:
--   Aprime Inf G: tube Chart of
-- statement:
--   The Aprime Inf G construction uses the tube Chart of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpChartC.lean#L14-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpChartC.lean#L14-L121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpChartC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.AprimeInfG.tubeChart_of (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → G) (χ : EuclideanSpace ℝ η → H) {r0 : ℝ} (hr0 : 0 < r0)
    (hκc : ContinuousOn κ (ball 0 r0)) (hχc : ContinuousOn χ (ball 0 r0)) (hχi : InjOn χ (ball 0 r0))
    (hinj : ∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0,
      (κ a)⁻¹ * κ b ∈ H → a = b)
    (φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → G) (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ)
    (hφ : ∀ A ⊆ U, MeasurableSet A → μ (φ '' A) = ∫⁻ z in A, ENNReal.ofReal (D z))
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
    (F' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (hF : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, HasFDerivWithinAt F (F' p) (ball 0 r0) p)
    (hFi : InjOn F (ball 0 r0)) (hFU : F '' ball 0 r0 ⊆ U)
    (hΦ : ∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, κ p.1 * (χ p.2 : G) = φ (F p))
    (e : EuclideanSpace ℝ η → ℝ)
    (hνH : ∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)) :
    TubeChart μ H ν κ χ r0 (fun p => |(F' p).det| * D (F p)) e := by sorry
