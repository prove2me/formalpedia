-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Measures_modularCharacter_borel__7687e76de9c2
-- name    : P2M_GroundTheory_Automorphic_Measures_modularCharacter_borel__7687e76de9c2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:01.480805+00:00
-- url     : https://prove2.me/theorems/b901a1e6-4e13-4249-92cf-67667510a6e9
-- title:
--   P2 M Ground Theory Automorphic Measures modular Character borel  7687e76de9c2: P2 M Ground Theory Automorphic Measures modular Character borel  7687e76de9c2
-- statement:
--   The P2 M Ground Theory Automorphic Measures modular Character borel  7687e76de9c2 construction uses the P2 M Ground Theory Automorphic Measures modular Character borel  7687e76de9c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L337-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L337-L340

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

theorem P2M_GroundTheory_Automorphic_Measures_modularCharacter_borel__7687e76de9c2 (b : borel F n) :
    modularCharacter b = ∏ i : Fin n,
      modulus (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i) ^ ((n : ℤ) - 1 - 2 * i) := by sorry

alias «GroundTheory».«Automorphic».«Measures».«modularCharacter_borel'» := P2M_GroundTheory_Automorphic_Measures_modularCharacter_borel__7687e76de9c2
