-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_Hyp_ext__f02e101d5eb6
-- name    : P2M_GlobalTheory_IndLine_Iwasawa_Hyp_ext__f02e101d5eb6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:23.145384+00:00
-- url     : https://prove2.me/theorems/694f2897-75a5-4897-bec6-5abf46efd245
-- title:
--   P2 M Global Theory Ind Line Iwasawa Hyp ext  f02e101d5eb6: P2 M Global Theory Ind Line Iwasawa Hyp ext  f02e101d5eb6
-- statement:
--   The P2 M Global Theory Ind Line Iwasawa Hyp ext  f02e101d5eb6 construction uses the P2 M Global Theory Ind Line Iwasawa Hyp ext  f02e101d5eb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L289-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L289-L292

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

theorem P2M_GlobalTheory_IndLine_Iwasawa_Hyp_ext__f02e101d5eb6 {g g' : Matrix m m A} (hx : g *ᵥ x = g' *ᵥ x) (hy : g *ᵥ y = g' *ᵥ y) (hι : g * ι = g' * ι) : g = g' := by sorry

alias «GlobalTheory».«IndLine».«Iwasawa».«Hyp».«ext'» := P2M_GlobalTheory_IndLine_Iwasawa_Hyp_ext__f02e101d5eb6
