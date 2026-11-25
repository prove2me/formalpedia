-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_mem_span_xi_pow_of_forall
-- name    : Reformulated.AutPerF.Ainf.mem_span_xi_pow_of_forall
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:33:02.958748+00:00
-- url     : https://prove2.me/theorems/3a37856d-79d8-460f-99be-de2d3faae8fc
-- title:
--   Ainf: mem span xi pow of forall
-- statement:
--   The Ainf construction uses the mem span xi pow of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L318-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L318-L326

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
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
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]

theorem Reformulated.AutPerF.Ainf.mem_span_xi_pow_of_forall (ϖ : PFlat p R) {n : ℕ} {x : Ainf p R}
    (h : ∀ k : ℕ, x ∈ span {(p : Ainf p R)} ^ k ⊔ span {xi ϖ} ^ n) : x ∈ span {xi ϖ} ^ n := by sorry
