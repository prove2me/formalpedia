-- Prove2me | Theorems.Thm_P2M_Reformulated_AutPerF_eval__mem_map_of_evalOne_bfbf0b8937ef
-- name    : P2M_Reformulated_AutPerF_eval__mem_map_of_evalOne_bfbf0b8937ef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:18:25.361104+00:00
-- url     : https://prove2.me/theorems/c6b5a7aa-7f96-480b-8241-910b92a40c0a
-- title:
--   P2 M Reformulated Aut Per F eval  mem map of eval One bfbf0b8937ef: P2 M Reformulated Aut Per F eval  mem map of eval One bfbf0b8937ef
-- statement:
--   The P2 M Reformulated Aut Per F eval  mem map of eval One bfbf0b8937ef construction uses the P2 M Reformulated Aut Per F eval  mem map of eval One bfbf0b8937ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L192-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L192-L205

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]

theorem P2M_Reformulated_AutPerF_eval__mem_map_of_evalOne_bfbf0b8937ef {A : Type*} [CommRing A] (I : Ideal A) {y : AdicCompletion I A}
    (hy : AdicCompletion.evalOneₐ I y = 0) (n : ℕ) :
    AdicCompletion.evalₐ I n y ∈ I.map (Ideal.Quotient.mk (I ^ n)) := by sorry

alias «Reformulated».«AutPerF».«evalₐ_mem_map_of_evalOne» := P2M_Reformulated_AutPerF_eval__mem_map_of_evalOne_bfbf0b8937ef
