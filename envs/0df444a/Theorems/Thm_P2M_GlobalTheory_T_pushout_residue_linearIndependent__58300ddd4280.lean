-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_pushout_residue_linearIndependent__58300ddd4280
-- name    : P2M_GlobalTheory_T_pushout_residue_linearIndependent__58300ddd4280
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:54.622999+00:00
-- url     : https://prove2.me/theorems/cfcaf262-3452-4efe-9bac-e472973d895a
-- title:
--   P2 M Global Theory T pushout residue linear Independent  58300ddd4280: P2 M Global Theory T pushout residue linear Independent  58300ddd4280
-- statement:
--   The P2 M Global Theory T pushout residue linear Independent  58300ddd4280 construction uses the P2 M Global Theory T pushout residue linear Independent  58300ddd4280 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PushoutResidueLinearIndependentStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PushoutResidueLinearIndependentStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PushoutResidueLinearIndependent
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PushoutResidueLinearIndependentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_pushout_residue_linearIndependent__58300ddd4280 : ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by sorry

alias «GlobalTheory».«T».«pushout_residue_linearIndependent'» := P2M_GlobalTheory_T_pushout_residue_linearIndependent__58300ddd4280
