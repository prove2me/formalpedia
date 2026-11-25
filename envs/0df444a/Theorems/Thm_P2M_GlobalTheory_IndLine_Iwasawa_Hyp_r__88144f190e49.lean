-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_r__88144f190e49
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Hyp_r__88144f190e49
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:06.654138+00:00
-- url     : https://prove2.me/theorems/06809943-39ea-4861-848d-7ea5f83f681c
-- title:
--   P2 M Global Theory Ind Line Iwasawa Hyp r  88144f190e49: P2 M Global Theory Ind Line Iwasawa Hyp r  88144f190e49
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Hyp r  88144f190e49 construction uses the P2 M Global Theory Ind Line Iwasawa Hyp r  88144f190e49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L311-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L311-L312

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
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h

theorem P2M_GlobalTheory_IndLine_Iwasawa_Hyp_r__88144f190e49 : (1 - prX c J x y - prY c J x y) * ι = ι := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Hyp».«rι» := P2M_GlobalTheory_IndLine_Iwasawa_Hyp_r__88144f190e49
