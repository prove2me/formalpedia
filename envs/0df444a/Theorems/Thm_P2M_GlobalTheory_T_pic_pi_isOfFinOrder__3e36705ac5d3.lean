-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_pic_pi_isOfFinOrder__3e36705ac5d3
-- name    : P2M_GlobalTheory_T_pic_pi_isOfFinOrder__3e36705ac5d3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:34.915867+00:00
-- url     : https://prove2.me/theorems/de987b04-eb0b-4036-a1b3-aa60c568b5b1
-- title:
--   P2 M Global Theory T pic pi is Of Fin Order  3e36705ac5d3: P2 M Global Theory T pic pi is Of Fin Order  3e36705ac5d3
-- statement:
--   The P2 M Global Theory T pic pi is Of Fin Order  3e36705ac5d3 construction uses the P2 M Global Theory T pic pi is Of Fin Order  3e36705ac5d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicPiIsOfFinOrderStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PicPiIsOfFinOrderStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_pic_pi_isOfFinOrder__3e36705ac5d3 : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)], (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) → ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by sorry

alias «GlobalTheory».«T».«pic_pi_isOfFinOrder'» := P2M_GlobalTheory_T_pic_pi_isOfFinOrder__3e36705ac5d3
