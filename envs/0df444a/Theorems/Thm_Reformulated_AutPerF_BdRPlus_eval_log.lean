-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_eval_log
-- name    : Reformulated.AutPerF.BdRPlus.eval_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:22.899875+00:00
-- url     : https://prove2.me/theorems/dd2202df-91db-4fad-9e1e-a7cc0ab245bf
-- title:
--   Bd RPlus: eval log
-- statement:
--   The Bd RPlus construction uses the eval log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L143-L145

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
open Reformulated.AutPerF.BdRPlus
variable {p R}

theorem Reformulated.AutPerF.BdRPlus.eval_log (u : BdRPlus p R) (hu : theta p R u = 1) (n : ℕ) :
    eval p R n (log u hu) = truncLog n (eval p R n (u - 1)) := by sorry
