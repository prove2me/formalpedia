-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_isOpen_noZeroBlock_a770c8a08c0b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_isOpen_noZeroBlock_a770c8a08c0b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:03.668576+00:00
-- url     : https://prove2.me/theorems/7fd76e88-a895-45ec-ba48-61579a686453
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist is Open no Zero Block a770c8a08c0b: P2 M Ground Theory Heights  Heights Inter Semipositive Twist is Open no Zero Block a770c8a08c0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist is Open no Zero Block a770c8a08c0b construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist is Open no Zero Block a770c8a08c0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L24-L30

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_isOpen_noZeroBlock_a770c8a08c0b : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«isOpen_noZeroBlock» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_isOpen_noZeroBlock_a770c8a08c0b
