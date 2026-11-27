-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_levi___78c2cece847b
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Hyp_levi___78c2cece847b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:30.168738+00:00
-- url     : https://prove2.me/theorems/77fc7a81-30dc-4610-a1d4-9fc0d41dfb2b
-- title:
--   P2 M Global Theory Ind Line Iwasawa Hyp levi   78c2cece847b: P2 M Global Theory Ind Line Iwasawa Hyp levi   78c2cece847b
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Hyp levi   78c2cece847b construction uses the P2 M Global Theory Ind Line Iwasawa Hyp levi   78c2cece847b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L348-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L348-L352

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

theorem P2M_GlobalTheory_IndLine_Iwasawa_Hyp_levi___78c2cece847b {g : Matrix m m A} (hp : g * prX c J x y = prX c J x y * g) (hq : g * prY c J x y = prY c J x y * g) :
    g * ι = ι * (ι' * g * ι) := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Hyp».«levi_ι» := P2M_GlobalTheory_IndLine_Iwasawa_Hyp_levi___78c2cece847b
