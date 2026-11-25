-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_eval_eq_zero_iff
-- name    : Reformulated.AutPerF.Acris.eval_eq_zero_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:21:50.46594+00:00
-- url     : https://prove2.me/theorems/59ebf011-ff77-4bba-909c-33a4130a4a82
-- title:
--   Acris: eval eq zero iff
-- statement:
--   The Acris construction uses the eval eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L104-L107

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

theorem Reformulated.AutPerF.Acris.eval_eq_zero_iff (n : ℕ) (x : Acris p R) : eval p R n x = 0 ↔ (p : Acris p R) ^ n ∣ x := by sorry
