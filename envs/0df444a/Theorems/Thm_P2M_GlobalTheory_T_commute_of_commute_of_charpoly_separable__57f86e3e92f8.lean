-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_commute_of_commute_of_charpoly_separable__57f86e3e92f8
-- name    : P2M_GlobalTheory_T_commute_of_commute_of_charpoly_separable__57f86e3e92f8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:09.99494+00:00
-- url     : https://prove2.me/theorems/ae047a7c-352a-4139-9f7f-c9c1d7a88ec2
-- title:
--   P2 M Global Theory T commute of commute of charpoly separable  57f86e3e92f8: P2 M Global Theory T commute of commute of charpoly separable  57f86e3e92f8
-- statement:
--   The P2 M Global Theory T commute of commute of charpoly separable  57f86e3e92f8 construction uses the P2 M Global Theory T commute of commute of charpoly separable  57f86e3e92f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommuteOfCommuteSeparableCharpolyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommuteOfCommuteSeparableCharpolyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommuteOfCommuteSeparableCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommuteOfCommuteSeparableCharpolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_commute_of_commute_of_charpoly_separable__57f86e3e92f8 : ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable → a * y = y * a → b * y = y * b → a * b = b * a := by sorry

alias «GlobalTheory».«T».«commute_of_commute_of_charpoly_separable'» := P2M_GlobalTheory_T_commute_of_commute_of_charpoly_separable__57f86e3e92f8
