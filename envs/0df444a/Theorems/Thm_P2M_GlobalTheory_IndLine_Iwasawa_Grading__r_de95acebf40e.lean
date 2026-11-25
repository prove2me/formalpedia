-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Grading__r_de95acebf40e
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Grading__r_de95acebf40e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:08.184206+00:00
-- url     : https://prove2.me/theorems/9b66909f-19c7-4055-988d-4e6ee88e8096
-- title:
--   P2 M Global Theory Ind Line Iwasawa Grading  r de95acebf40e: P2 M Global Theory Ind Line Iwasawa Grading  r de95acebf40e
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Grading  r de95acebf40e construction uses the P2 M Global Theory Ind Line Iwasawa Grading  r de95acebf40e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L88-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {R : Type} [Ring R]
open GlobalTheory.IndLine.Iwasawa.Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h

theorem P2M_GlobalTheory_IndLine_Iwasawa_Grading__r_de95acebf40e : θ * r = r * θ := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Grading».«θr» := P2M_GlobalTheory_IndLine_Iwasawa_Grading__r_de95acebf40e
