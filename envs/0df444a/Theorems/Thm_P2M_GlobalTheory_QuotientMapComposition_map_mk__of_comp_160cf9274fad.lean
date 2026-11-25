-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QuotientMapComposition_map_mk__of_comp_160cf9274fad
-- name    : P2M_GlobalTheory_QuotientMapComposition_map_mk__of_comp_160cf9274fad
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:57.712804+00:00
-- url     : https://prove2.me/theorems/9b6dac41-bd21-48df-8aeb-f3f10253f52b
-- title:
--   P2 M Global Theory Quotient Map Composition map mk  of comp 160cf9274fad: P2 M Global Theory Quotient Map Composition map mk  of comp 160cf9274fad
-- statement:
--   The P2 M Global Theory Quotient Map Composition map mk  of comp 160cf9274fad construction uses the P2 M Global Theory Quotient Map Composition map mk  of comp 160cf9274fad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMkOfComp.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapMkOfComp.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMkOfComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.QuotientMapComposition

theorem P2M_GlobalTheory_QuotientMapComposition_map_mk__of_comp_160cf9274fad {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (f : A →+* R) (F : LA →+* LR)
    (h : F.comp (algebraMap A LA) = (algebraMap R LR).comp f) (M : Submonoid A) [IsLocalization M LA]
    (N : Submonoid R) [IsLocalization N LR] (a : A) (m : M) (n : N) (hn : (n : R) = f m) :
    F (IsLocalization.mk' LA a m) = IsLocalization.mk' LR (f a) n := by sorry

alias «GlobalTheory».«QuotientMapComposition».«map_mk'_of_comp» := P2M_GlobalTheory_QuotientMapComposition_map_mk__of_comp_160cf9274fad
