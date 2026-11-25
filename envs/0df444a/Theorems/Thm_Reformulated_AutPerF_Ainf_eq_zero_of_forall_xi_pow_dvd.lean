-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_eq_zero_of_forall_xi_pow_dvd
-- name    : Reformulated.AutPerF.Ainf.eq_zero_of_forall_xi_pow_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:12:33.202827+00:00
-- url     : https://prove2.me/theorems/bb8c2f46-0c3d-4b32-93c2-c37ba5acaba1
-- title:
--   Ainf: eq zero of forall xi pow dvd
-- statement:
--   The Ainf construction uses the eq zero of forall xi pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L328-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L328-L345

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

theorem Reformulated.AutPerF.Ainf.eq_zero_of_forall_xi_pow_dvd (ϖ : PFlat p R) {x : Ainf p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 := by sorry
