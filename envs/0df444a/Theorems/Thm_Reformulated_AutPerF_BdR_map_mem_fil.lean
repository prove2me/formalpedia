-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdR_map_mem_fil
-- name    : Reformulated.AutPerF.BdR.map_mem_fil
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:02.371559+00:00
-- url     : https://prove2.me/theorems/f31d6c37-c284-4690-9297-16881a8da37d
-- title:
--   Bd R: map mem fil
-- statement:
--   The Bd R construction uses the map mem fil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L137-L142

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

theorem Reformulated.AutPerF.BdR.map_mem_fil (e : R ≃+* S) {i : ℤ} {x : BdR p R} (hx : x ∈ fil p R i) :
    map p e x ∈ fil p S i := by sorry
