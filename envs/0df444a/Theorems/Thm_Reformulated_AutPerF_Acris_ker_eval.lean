-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_ker_eval
-- name    : Reformulated.AutPerF.Acris.ker_eval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:21:20.916711+00:00
-- url     : https://prove2.me/theorems/ba3d27ed-52c8-5715-b6d2-de92039bfaa1
-- title:
--   Acris: ker eval
-- statement:
--   The Acris construction uses the ker eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L109-L111

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

theorem Reformulated.AutPerF.Acris.ker_eval (n : ℕ) : RingHom.ker (eval p R n) = span {(p : Acris p R)} ^ n := by sorry
