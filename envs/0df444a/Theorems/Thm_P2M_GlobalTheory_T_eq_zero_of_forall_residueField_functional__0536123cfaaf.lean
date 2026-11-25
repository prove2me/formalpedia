-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_eq_zero_of_forall_residueField_functional__0536123cfaaf
-- name    : P2M_GlobalTheory_T_eq_zero_of_forall_residueField_functional__0536123cfaaf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:27.9682+00:00
-- url     : https://prove2.me/theorems/83d2b21a-580a-47ac-8b29-da74bc5827f7
-- title:
--   P2 M Global Theory T eq zero of forall residue Field functional  0536123cfaaf: P2 M Global Theory T eq zero of forall residue Field functional  0536123cfaaf
-- statement:
--   The P2 M Global Theory T eq zero of forall residue Field functional  0536123cfaaf construction uses the P2 M Global Theory T eq zero of forall residue Field functional  0536123cfaaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallResidueFieldFunctionalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallResidueFieldFunctionalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallResidueFieldFunctional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallResidueFieldFunctionalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_eq_zero_of_forall_residueField_functional__0536123cfaaf : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by sorry

alias «GlobalTheory».«T».«eq_zero_of_forall_residueField_functional'» := P2M_GlobalTheory_T_eq_zero_of_forall_residueField_functional__0536123cfaaf
