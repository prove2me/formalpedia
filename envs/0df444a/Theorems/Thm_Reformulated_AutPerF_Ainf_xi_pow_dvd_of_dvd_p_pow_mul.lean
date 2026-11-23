-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_xi_pow_dvd_of_dvd_p_pow_mul
-- name    : Reformulated.AutPerF.Ainf.xi_pow_dvd_of_dvd_p_pow_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:31.544553+00:00
-- url     : https://prove2.me/theorems/9b673230-4629-4c1f-b912-31dfd01a386b
-- title:
--   Ainf: xi pow dvd of dvd p pow mul
-- statement:
--   The Ainf construction uses the xi pow dvd of dvd p pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L292-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L292-L300

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

theorem Reformulated.AutPerF.Ainf.xi_pow_dvd_of_dvd_p_pow_mul (ϖ : PFlat p R) {n k : ℕ} {x : Ainf p R}
    (h : xi ϖ ^ n ∣ (p : Ainf p R) ^ k * x) : xi ϖ ^ n ∣ x := by sorry
