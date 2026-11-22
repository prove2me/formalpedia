-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Acris_eval_log
-- name    : Reformulated.AutPerF.Acris.eval_log
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:41.092019+00:00
-- url     : https://prove2.me/theorems/7feb37de-40b3-4e75-bc2f-8cfc10b79497
-- title:
--   Acris: eval log
-- statement:
--   The Acris construction uses the eval log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L238-L240

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
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
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Acris
variable {p R}

theorem Reformulated.AutPerF.Acris.eval_log (u : Ainf p R) (hu : Ainf.theta p R u = 1) {n N : ℕ} (hN : p ^ n ≤ N) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ (logPartial N u hu) := by sorry
