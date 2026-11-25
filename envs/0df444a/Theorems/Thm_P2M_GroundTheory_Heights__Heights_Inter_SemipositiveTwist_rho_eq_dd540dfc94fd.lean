-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_eq_dd540dfc94fd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_eq_dd540dfc94fd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:26.838115+00:00
-- url     : https://prove2.me/theorems/d9082eb1-a478-4619-a78a-d04b76b6ba0a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho eq dd540dfc94fd: P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho eq dd540dfc94fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho eq dd540dfc94fd construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho eq dd540dfc94fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L48-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_eq_dd540dfc94fd (k : K) (y : (Σ k, ι k) → ℂ) :
    (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«rho_eq» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_eq_dd540dfc94fd
