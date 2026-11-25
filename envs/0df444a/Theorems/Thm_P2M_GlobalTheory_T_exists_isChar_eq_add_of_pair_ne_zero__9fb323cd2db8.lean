-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_isChar_eq_add_of_pair_ne_zero__9fb323cd2db8
-- name    : P2M_GlobalTheory_T_exists_isChar_eq_add_of_pair_ne_zero__9fb323cd2db8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:42.627111+00:00
-- url     : https://prove2.me/theorems/316bf3a3-5d61-4173-851c-ce5b2f9c57dd
-- title:
--   P2 M Global Theory T exists is Char eq add of pair ne zero  9fb323cd2db8: P2 M Global Theory T exists is Char eq add of pair ne zero  9fb323cd2db8
-- statement:
--   The P2 M Global Theory T exists is Char eq add of pair ne zero  9fb323cd2db8 construction uses the P2 M Global Theory T exists is Char eq add of pair ne zero  9fb323cd2db8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIsCharEqAddOfPairNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIsCharEqAddOfPairNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIsCharEqAddOfPairNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIsCharEqAddOfPairNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_isChar_eq_add_of_pair_ne_zero__9fb323cd2db8 : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by sorry

alias «GlobalTheory».«T».«exists_isChar_eq_add_of_pair_ne_zero'» := P2M_GlobalTheory_T_exists_isChar_eq_add_of_pair_ne_zero__9fb323cd2db8
