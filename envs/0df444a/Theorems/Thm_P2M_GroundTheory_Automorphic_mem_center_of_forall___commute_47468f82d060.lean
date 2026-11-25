-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_mem_center_of_forall___commute_47468f82d060
-- name    : P2M_GroundTheory_Automorphic_mem_center_of_forall___commute_47468f82d060
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:20.418328+00:00
-- url     : https://prove2.me/theorems/7db9ba68-ba27-4813-a3f4-6b1414d77be6
-- title:
--   P2 M Ground Theory Automorphic mem center of forall   commute 47468f82d060: P2 M Ground Theory Automorphic mem center of forall   commute 47468f82d060
-- statement:
--   The P2 M Ground Theory Automorphic mem center of forall   commute 47468f82d060 construction uses the P2 M Ground Theory Automorphic mem center of forall   commute 47468f82d060 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Casimir.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Casimir.lean#L16-L27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem P2M_GroundTheory_Automorphic_mem_center_of_forall___commute_47468f82d060 {z : UniversalEnvelopingAlgebra ℝ L}
    (hz : ∀ x : L, UniversalEnvelopingAlgebra.ι ℝ x * z = z * UniversalEnvelopingAlgebra.ι ℝ x) :
    z ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ L) := by sorry

alias «GroundTheory».«Automorphic».«mem_center_of_forall_ι_commute» := P2M_GroundTheory_Automorphic_mem_center_of_forall___commute_47468f82d060
