-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Measures_modularCharacter_blockUpper_of_mem_borel__c97a33a12eeb
-- name    : P2M_GroundTheory_Automorphic_Measures_modularCharacter_blockUpper_of_mem_borel__c97a33a12eeb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:18.582016+00:00
-- url     : https://prove2.me/theorems/598fd26b-0dd7-4e12-aeb6-ef9e45d7ce2e
-- title:
--   P2 M Ground Theory Automorphic Measures modular Character block Upper of mem borel  c97a33a12eeb: P2 M Ground Theory Automorphic Measures modular Character block Upper of mem borel  c97a33a12eeb
-- statement:
--   The P2 M Ground Theory Automorphic Measures modular Character block Upper of mem borel  c97a33a12eeb construction uses the P2 M Ground Theory Automorphic Measures modular Character block Upper of mem borel  c97a33a12eeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L262-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L262-L303

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}

theorem P2M_GroundTheory_Automorphic_Measures_modularCharacter_blockUpper_of_mem_borel__c97a33a12eeb (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    modularCharacter p = ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
      modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by sorry

alias «GroundTheory».«Automorphic».«Measures».«modularCharacter_blockUpper_of_mem_borel'» := P2M_GroundTheory_Automorphic_Measures_modularCharacter_blockUpper_of_mem_borel__c97a33a12eeb
