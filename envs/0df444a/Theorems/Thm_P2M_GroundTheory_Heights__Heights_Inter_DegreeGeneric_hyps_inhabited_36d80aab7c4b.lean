-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:04.268528+00:00
-- url     : https://prove2.me/theorems/c0fa94e4-6ea5-4e41-9a60-5f629f20f006
-- title:
--   P2 M Ground Theory Heights  Heights Inter Degree Generic hyps inhabited 36d80aab7c4b: P2 M Ground Theory Heights  Heights Inter Degree Generic hyps inhabited 36d80aab7c4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Degree Generic hyps inhabited 36d80aab7c4b construction uses the P2 M Ground Theory Heights  Heights Inter Degree Generic hyps inhabited 36d80aab7c4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/Statements.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/Statements.lean#L48-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧ ∀ j, IsSmoothHerm (![fsLine 2] j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DegreeGeneric».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b
