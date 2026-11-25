-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_continuousOn_segre_lift_63fa5bef8928
-- name    : P2M_GroundTheory_Heights__Heights_Targets_continuousOn_segre_lift_63fa5bef8928
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:29.093349+00:00
-- url     : https://prove2.me/theorems/26d93e72-2d11-5fab-88ef-6f0d59fff56c
-- title:
--   P2 M Ground Theory Heights  Heights Targets continuous On segre lift 63fa5bef8928: P2 M Ground Theory Heights  Heights Targets continuous On segre lift 63fa5bef8928
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets continuous On segre lift 63fa5bef8928 construction uses the P2 M Ground Theory Heights  Heights Targets continuous On segre lift 63fa5bef8928 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L30-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem P2M_GroundTheory_Heights__Heights_Targets_continuousOn_segre_lift_63fa5bef8928 {e n : ℕ} (R : AnLogRes P J e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x₀ : R.X) :
    ContinuousOn (fun x => Ψ (segre (R.lift x₀ x))) (R.U x₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«continuousOn_segre_lift» := P2M_GroundTheory_Heights__Heights_Targets_continuousOn_segre_lift_63fa5bef8928
