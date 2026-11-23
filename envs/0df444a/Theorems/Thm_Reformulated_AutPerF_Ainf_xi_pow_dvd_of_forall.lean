-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_xi_pow_dvd_of_forall
-- name    : Reformulated.AutPerF.Ainf.xi_pow_dvd_of_forall
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:26.461238+00:00
-- url     : https://prove2.me/theorems/17c241a7-57a4-4a09-aba7-47e0291dcec7
-- title:
--   Ainf: xi pow dvd of forall
-- statement:
--   The Ainf construction uses the xi pow dvd of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L302-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L302-L316

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

theorem Reformulated.AutPerF.Ainf.xi_pow_dvd_of_forall (ϖ : PFlat p R) {n : ℕ} {x : Ainf p R}
    (h : ∀ k : ℕ, ∃ a b, x = (p : Ainf p R) ^ k * a + xi ϖ ^ n * b) : xi ϖ ^ n ∣ x := by sorry
