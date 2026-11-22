-- Prove2me | Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- name    : Reformulated.AutPerF.awayMap_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:58.113136+00:00
-- url     : https://prove2.me/theorems/c4d8f601-a687-42c5-848d-3d34c2ce77a0
-- title:
--   Aut Per F: away Map algebra Map
-- statement:
--   The Aut Per F construction uses the away Map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L320-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L320-L322

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
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
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]
variable {R S U}
omit [Fact p.Prime]

theorem Reformulated.AutPerF.awayMap_algebraMap {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) : awayMap p f (algebraMap _ _ x) = algebraMap _ _ (f x) := by sorry
