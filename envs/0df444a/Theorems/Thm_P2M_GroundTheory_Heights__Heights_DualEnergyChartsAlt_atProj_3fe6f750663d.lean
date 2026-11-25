-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEnergyChartsAlt_atProj_3fe6f750663d
-- name    : P2M_GroundTheory_Heights__Heights_DualEnergyChartsAlt_atProj_3fe6f750663d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:38.046815+00:00
-- url     : https://prove2.me/theorems/d0bbbf97-8e28-49df-aefc-2bf833c8550f
-- title:
--   P2 M Ground Theory Heights  Heights Dual Energy Charts Alt at Proj 3fe6f750663d: P2 M Ground Theory Heights  Heights Dual Energy Charts Alt at Proj 3fe6f750663d
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Energy Charts Alt at Proj 3fe6f750663d construction uses the P2 M Ground Theory Heights  Heights Dual Energy Charts Alt at Proj 3fe6f750663d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEnergyCharts.lean#L27-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEnergyCharts.lean#L27-L171

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergyCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEnergyCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualEnergyChartsAlt
open StandardDualMassAtPoint DualGeometricDegreeCharts
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}

theorem P2M_GroundTheory_Heights__Heights_DualEnergyChartsAlt_atProj_3fe6f750663d (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement)
    (hInt : ChartEnergyIntegrable.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)) (hΨ : IsGoodProj (dualIdeal b) Ψ) :
    (∀ σ, Function.Bijective (chartMat hOf b hb hΨ σ).mulVec) ∧ ∀ k : ℕ,
      ptsIntegralAt (e := D) (dualIdeal b) Ψ
          (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
        ∑ σ : K →+* ℂ, chartMixedEnergy ((chartMat hOf b hb hΨ σ)ᴴ * F.metric σ * chartMat hOf b hb hΨ σ)
          ((chartMat hOf b hb hΨ σ)ᴴ * chartMat hOf b hb hΨ σ) k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualEnergyChartsAlt».«atProj» := P2M_GroundTheory_Heights__Heights_DualEnergyChartsAlt_atProj_3fe6f750663d
