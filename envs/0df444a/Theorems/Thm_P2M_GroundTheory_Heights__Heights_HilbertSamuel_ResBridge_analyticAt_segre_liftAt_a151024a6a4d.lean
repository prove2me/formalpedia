-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_segre_liftAt_a151024a6a4d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_segre_liftAt_a151024a6a4d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:30:01.536731+00:00
-- url     : https://prove2.me/theorems/47d4105b-90dd-4316-809a-09b6804ef8ef
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge analytic At segre lift At a151024a6a4d: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge analytic At segre lift At a151024a6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge analytic At segre lift At a151024a6a4d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge analytic At segre lift At a151024a6a4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L61-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_segre_liftAt_a151024a6a4d (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v)))) u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«analyticAt_segre_liftAt» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_analyticAt_segre_liftAt_a151024a6a4d
