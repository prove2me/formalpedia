-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bcris_logTeich_mul
-- name    : Reformulated.AutPerF.Bcris.logTeich_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:21:37.149368+00:00
-- url     : https://prove2.me/theorems/08afe7eb-1736-5093-b737-23fdc20fc023
-- title:
--   Bcris: log Teich mul
-- statement:
--   The Bcris construction uses the log Teich mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L256-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L256-L257

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

theorem Reformulated.AutPerF.Bcris.logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by sorry
