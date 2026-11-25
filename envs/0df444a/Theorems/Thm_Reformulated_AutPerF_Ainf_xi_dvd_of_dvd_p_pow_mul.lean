-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_xi_dvd_of_dvd_p_pow_mul
-- name    : Reformulated.AutPerF.Ainf.xi_dvd_of_dvd_p_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:25.798803+00:00
-- url     : https://prove2.me/theorems/e0a70d36-afb0-4336-b657-889dd5edaff3
-- title:
--   Ainf: xi dvd of dvd p pow mul
-- statement:
--   The Ainf construction uses the xi dvd of dvd p pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L287-L290

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

theorem Reformulated.AutPerF.Ainf.xi_dvd_of_dvd_p_pow_mul (ϖ : PFlat p R) {x : Ainf p R} {k : ℕ}
    (h : xi ϖ ∣ (p : Ainf p R) ^ k * x) : xi ϖ ∣ x := by sorry
