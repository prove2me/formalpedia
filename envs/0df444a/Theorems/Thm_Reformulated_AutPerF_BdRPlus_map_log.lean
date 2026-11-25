-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_map_log
-- name    : Reformulated.AutPerF.BdRPlus.map_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:47.6945+00:00
-- url     : https://prove2.me/theorems/1a1f5bcc-45a2-4483-bb8c-d25bbf5cf7fd
-- title:
--   Bd RPlus: map log
-- statement:
--   The Bd RPlus construction uses the map log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean#L87-L90

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_map

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

theorem Reformulated.AutPerF.BdRPlus.map_log (f : R →+* S) (u : BdRPlus p R) (hu : theta p R u = 1) :
    map p f (log u hu) = log (map p f u) (by rw [theta_map, hu, map_one]) := by sorry
