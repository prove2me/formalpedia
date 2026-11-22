-- Prove2me | Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
-- name    : Reformulated.AutPerF.fracWittLift_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:47.280229+00:00
-- url     : https://prove2.me/theorems/3143fcfb-1c6a-4184-90b6-f72060b34ea4
-- title:
--   Aut Per F: frac Witt Lift algebra Map
-- statement:
--   The Aut Per F construction uses the frac Witt Lift algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L132-L134

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]

theorem Reformulated.AutPerF.fracWittLift_algebraMap {B : Type*} [CommRing B] (f : WittVector p k →+* B)
    (h : IsUnit (p : B)) (a : WittVector p k) : fracWittLift p f h (algebraMap _ _ a) = f a := by sorry
