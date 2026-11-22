-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_mapEquiv_apply
-- name    : Reformulated.AutPerF.BdRPlus.mapEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:19.128802+00:00
-- url     : https://prove2.me/theorems/b83cc79c-9333-48d7-b9f2-9c06c62a9252
-- title:
--   Bd RPlus: map Equiv apply
-- statement:
--   The Bd RPlus construction uses the map Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L98-L99

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

theorem Reformulated.AutPerF.BdRPlus.mapEquiv_apply (e : R ≃+* S) (x : BdRPlus p R) :
    mapEquiv p e x = map p (e : R →+* S) x := by sorry

attribute [defeq] Reformulated.AutPerF.BdRPlus.mapEquiv_apply
