-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_ext_eval
-- name    : Reformulated.AutPerF.BdRPlus.ext_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:19.765891+00:00
-- url     : https://prove2.me/theorems/974c4be6-d903-4778-b7e7-c82c2368226b
-- title:
--   Bd RPlus: ext eval
-- statement:
--   The Bd RPlus construction uses the ext eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L122-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L122-L123

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

theorem Reformulated.AutPerF.BdRPlus.ext_eval {x y : BdRPlus p R} (h : ∀ n, eval p R n x = eval p R n y) : x = y := by sorry
