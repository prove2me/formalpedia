-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_map_map
-- name    : Reformulated.AutPerF.Tilt.map_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:19.410013+00:00
-- url     : https://prove2.me/theorems/82bda132-3ab1-4492-ab47-73f4c3e675fc
-- title:
--   Tilt: map map
-- statement:
--   The Tilt construction uses the map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L114-L119

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
open Reformulated.AutPerF.Tilt
variable {p}

theorem Reformulated.AutPerF.Tilt.map_map (f : R →+* S) (g : S →+* U) (x : Tilt p R) :
    map p g (map p f x) = map p (g.comp f) x := by sorry
