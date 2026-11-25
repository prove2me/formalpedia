-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_map_logTeich
-- name    : Reformulated.AutPerF.BdRPlus.map_logTeich
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:39:23.203859+00:00
-- url     : https://prove2.me/theorems/6e676958-5c95-4ee0-bd9c-1a85c5476ca6
-- title:
--   Bd RPlus: map log Teich
-- statement:
--   The Bd RPlus construction uses the map log Teich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamLog.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamLog.lean#L133-L136

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Polynomial
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Reformulated.AutPerF.BdRPlus

theorem Reformulated.AutPerF.BdRPlus.map_logTeich (f : R →+* S) (η : tateModule p R) :
    map p f (logTeich η) = logTeich (tateModule.map p f η) := by sorry
