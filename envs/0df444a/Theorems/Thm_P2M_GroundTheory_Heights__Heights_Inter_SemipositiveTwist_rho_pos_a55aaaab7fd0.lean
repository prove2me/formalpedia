-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_pos_a55aaaab7fd0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_pos_a55aaaab7fd0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:40.746275+00:00
-- url     : https://prove2.me/theorems/7daf5128-9b49-4fb0-bde4-475677cbda0b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho pos a55aaaab7fd0: P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho pos a55aaaab7fd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho pos a55aaaab7fd0 construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist rho pos a55aaaab7fd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L44-L46

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_pos_a55aaaab7fd0 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«rho_pos» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_pos_a55aaaab7fd0
