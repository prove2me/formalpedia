-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_eq_zero_iff
-- name    : Reformulated.AutPerF.BdRPlus.theta_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:37.21422+00:00
-- url     : https://prove2.me/theorems/b103d3e5-27db-4c5c-a294-b77ab1fe40c6
-- title:
--   Bd RPlus: theta eq zero iff
-- statement:
--   The Bd RPlus construction uses the theta eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L132-L134

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

theorem Reformulated.AutPerF.BdRPlus.theta_eq_zero_iff (x : BdRPlus p R) :
    theta p R x = 0 ↔ AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x = 0 := by sorry
