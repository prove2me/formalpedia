-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_map_mem_fil
-- name    : Reformulated.AutPerF.BdRPlus.map_mem_fil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:25.047295+00:00
-- url     : https://prove2.me/theorems/bf1de1cc-b43b-4768-91a1-c3ea63060fde
-- title:
--   Bd RPlus: map mem fil
-- statement:
--   The Bd RPlus construction uses the map mem fil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L81-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L81-L85

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
open Reformulated.AutPerF.BdRPlus
variable {p}

theorem Reformulated.AutPerF.BdRPlus.map_mem_fil (f : R →+* S) {n : ℕ} {x : BdRPlus p R} (hx : x ∈ fil p R n) :
    map p f x ∈ fil p S n := by sorry
