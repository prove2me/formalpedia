-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_map_logFlat
-- name    : Reformulated.AutPerF.BdRPlus.map_logFlat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:29.685321+00:00
-- url     : https://prove2.me/theorems/31a9875b-4cfe-450f-aa91-25e33dcfa62f
-- title:
--   Bd RPlus: map log Flat
-- statement:
--   The Bd RPlus construction uses the map log Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamLog.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamLog.lean#L138-L141

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamLog
import Theorems.Thm_Reformulated_AutPerF_Bst_map_logFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.map_logFlat


set_option autoImplicit false
noncomputable section
open Ideal Polynomial
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Reformulated.AutPerF.BdRPlus

theorem Reformulated.AutPerF.BdRPlus.map_logFlat (f : R →+* S) (ϖ : PFlat p R) :
    map p f (logFlat ϖ) = logFlat (PFlat.map p f ϖ) := by sorry
