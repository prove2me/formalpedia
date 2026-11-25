-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isOpen_inter_subgroup_eq_one_0f3f786d713d
-- name    : P2M_GroundTheory_Heights__Theta_exists_isOpen_inter_subgroup_eq_one_0f3f786d713d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:47.433609+00:00
-- url     : https://prove2.me/theorems/3c3b18db-a48b-4424-88dc-2b1a3712c091
-- title:
--   P2 M Ground Theory Heights  Theta exists is Open inter subgroup eq one 0f3f786d713d: P2 M Ground Theory Heights  Theta exists is Open inter subgroup eq one 0f3f786d713d
-- statement:
--   The P2 M Ground Theory Heights  Theta exists is Open inter subgroup eq one 0f3f786d713d construction uses the P2 M Ground Theory Heights  Theta exists is Open inter subgroup eq one 0f3f786d713d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem P2M_GroundTheory_Heights__Theta_exists_isOpen_inter_subgroup_eq_one_0f3f786d713d (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ γ ∈ Γ, γ ∈ W → γ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_isOpen_inter_subgroup_eq_one» := P2M_GroundTheory_Heights__Theta_exists_isOpen_inter_subgroup_eq_one_0f3f786d713d
