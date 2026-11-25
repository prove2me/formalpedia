-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bcris_logTeich_pow
-- name    : Reformulated.AutPerF.Bcris.logTeich_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:21:14.682306+00:00
-- url     : https://prove2.me/theorems/ae8f50b0-06a7-4144-9f55-33ea8c3c5b02
-- title:
--   Bcris: log Teich pow
-- statement:
--   The Bcris construction uses the log Teich pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L261-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L261-L262

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
open Reformulated.AutPerF.Bcris

theorem Reformulated.AutPerF.Bcris.logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by sorry
