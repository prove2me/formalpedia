-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bcris_isUnit_logTeich
-- name    : Reformulated.AutPerF.Bcris.isUnit_logTeich
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:21:42.487807+00:00
-- url     : https://prove2.me/theorems/14a126f6-41b2-426d-af1f-ca0aa4b25487
-- title:
--   Bcris: is Unit log Teich
-- statement:
--   The Bcris construction uses the is Unit log Teich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L264-L266

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

theorem Reformulated.AutPerF.Bcris.isUnit_logTeich {ε : tateModule p R} (h : IsPrimitive ε) : IsUnit (logTeich ε) := by sorry
