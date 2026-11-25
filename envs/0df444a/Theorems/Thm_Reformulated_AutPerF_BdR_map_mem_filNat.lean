-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdR_map_mem_filNat
-- name    : Reformulated.AutPerF.BdR.map_mem_filNat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:31.467175+00:00
-- url     : https://prove2.me/theorems/44031ac1-95fb-4ab2-a8e7-86adbd5cde95
-- title:
--   Bd R: map mem fil Nat
-- statement:
--   The Bd R construction uses the map mem fil Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L132-L135

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
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
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
open Reformulated.AutPerF.BdR
variable {p}

theorem Reformulated.AutPerF.BdR.map_mem_filNat (e : R ≃+* S) {n : ℕ} {x : BdR p R} (hx : x ∈ filNat p R n) :
    map p e x ∈ filNat p S n := by sorry
