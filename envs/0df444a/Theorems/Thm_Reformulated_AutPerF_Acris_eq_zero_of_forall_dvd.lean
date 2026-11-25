-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_eq_zero_of_forall_dvd
-- name    : Reformulated.AutPerF.Acris.eq_zero_of_forall_dvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:21:37.69061+00:00
-- url     : https://prove2.me/theorems/e35dbefd-a1b4-4598-9c58-3c6795042448
-- title:
--   Acris: eq zero of forall dvd
-- statement:
--   The Acris construction uses the eq zero of forall dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L120-L121

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Acris

theorem Reformulated.AutPerF.Acris.eq_zero_of_forall_dvd {x : Acris p R} (h : ∀ n, (p : Acris p R) ^ n ∣ x) : x = 0 := by sorry
