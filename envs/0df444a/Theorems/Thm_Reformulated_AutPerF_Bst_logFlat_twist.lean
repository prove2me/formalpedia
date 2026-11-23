-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bst_logFlat_twist
-- name    : Reformulated.AutPerF.Bst.logFlat_twist
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:25.415875+00:00
-- url     : https://prove2.me/theorems/88022ff4-05dc-4cd9-8f2d-8555922dfc98
-- title:
--   Bst: log Flat twist
-- statement:
--   The Bst construction uses the log Flat twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L340-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L340-L343

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
open Reformulated.AutPerF.Bst
variable {p R}

theorem Reformulated.AutPerF.Bst.logFlat_twist (η : tateModule p R) (ϖ : PFlat p R) :
    logFlat (ϖ.twist η) = algebraMap _ _ (Bcris.logTeich η) + logFlat ϖ := by sorry
