-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_p__3c8c698927f0
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Hyp_p__3c8c698927f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:05.647789+00:00
-- url     : https://prove2.me/theorems/ce29aca5-1194-43b8-a086-8183b0cc9d0a
-- title:
--   P2 M Global Theory Ind Line Iwasawa Hyp p  3c8c698927f0: P2 M Global Theory Ind Line Iwasawa Hyp p  3c8c698927f0
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Hyp p  3c8c698927f0 construction uses the P2 M Global Theory Ind Line Iwasawa Hyp p  3c8c698927f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L273-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L273-L273

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

theorem P2M_GlobalTheory_IndLine_Iwasawa_Hyp_p__3c8c698927f0 : prX c J x y * ι = 0 := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Hyp».«pι» := P2M_GlobalTheory_IndLine_Iwasawa_Hyp_p__3c8c698927f0
