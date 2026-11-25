-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mulP_flat__3db101a2b691
-- name    : P2M_GlobalTheory_T_mulP_flat__3db101a2b691
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:21.759107+00:00
-- url     : https://prove2.me/theorems/6830a889-9784-4f50-b556-35717c8ad6fa
-- title:
--   P2 M Global Theory T mul P flat  3db101a2b691: P2 M Global Theory T mul P flat  3db101a2b691
-- statement:
--   The P2 M Global Theory T mul P flat  3db101a2b691 construction uses the P2 M Global Theory T mul P flat  3db101a2b691 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulPFlatStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulPFlatStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulPFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulPFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mulP_flat__3db101a2b691 : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by sorry

alias «GlobalTheory».«T».«mulP_flat'» := P2M_GlobalTheory_T_mulP_flat__3db101a2b691
