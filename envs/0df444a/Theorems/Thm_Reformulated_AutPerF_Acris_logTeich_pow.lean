-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_logTeich_pow
-- name    : Reformulated.AutPerF.Acris.logTeich_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:21:15.658521+00:00
-- url     : https://prove2.me/theorems/943f384a-bde9-5b89-9679-9e287c69d55b
-- title:
--   Acris: log Teich pow
-- statement:
--   The Acris construction uses the log Teich pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L239-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L239-L242

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

theorem Reformulated.AutPerF.Acris.logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by sorry
