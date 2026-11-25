-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19
-- name    : P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:42.292871+00:00
-- url     : https://prove2.me/theorems/e9413f7a-f412-512d-8888-d6d2c37365a2
-- title:
--   P2 M Ground Theory Automorphic Parabolic levi Proj mem congruence Subgroup  c7c7a3a01a19: P2 M Ground Theory Automorphic Parabolic levi Proj mem congruence Subgroup  c7c7a3a01a19
-- statement:
--   The P2 M Ground Theory Automorphic Parabolic levi Proj mem congruence Subgroup  c7c7a3a01a19 construction uses the P2 M Ground Theory Automorphic Parabolic levi Proj mem congruence Subgroup  c7c7a3a01a19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L124-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L124-L149

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19 {j : ℕ} {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ congruenceSubgroup F n j) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ congruenceSubgroup F n j := by sorry

alias «GroundTheory».«Automorphic».«Parabolic».«leviProj_mem_congruenceSubgroup'» := P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19
