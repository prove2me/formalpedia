-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_q__f8a8d2591abe
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Hyp_q__f8a8d2591abe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:07.844371+00:00
-- url     : https://prove2.me/theorems/7f33c939-ec5f-4cbf-9225-63914d79939a
-- title:
--   P2 M Global Theory Ind Line Iwasawa Hyp q  f8a8d2591abe: P2 M Global Theory Ind Line Iwasawa Hyp q  f8a8d2591abe
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Hyp q  f8a8d2591abe construction uses the P2 M Global Theory Ind Line Iwasawa Hyp q  f8a8d2591abe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L274-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L274-L274

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

theorem P2M_GlobalTheory_IndLine_Iwasawa_Hyp_q__f8a8d2591abe : prY c J x y * ι = 0 := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Hyp».«qι» := P2M_GlobalTheory_IndLine_Iwasawa_Hyp_q__f8a8d2591abe
