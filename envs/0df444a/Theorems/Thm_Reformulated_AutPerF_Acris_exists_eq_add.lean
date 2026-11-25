-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_exists_eq_add
-- name    : Reformulated.AutPerF.Acris.exists_eq_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:43.808434+00:00
-- url     : https://prove2.me/theorems/f25530a3-bda0-533c-944e-6345bc609804
-- title:
--   Acris: exists eq add
-- statement:
--   The Acris construction uses the exists eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L113-L118

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

theorem Reformulated.AutPerF.Acris.exists_eq_add (n : ℕ) (x : Acris p R) :
    ∃ (a : AcrisZero p R) (y : Acris p R), x = algebraMap _ _ a + (p : Acris p R) ^ n * y := by sorry
