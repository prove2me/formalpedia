-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_untilt_map
-- name    : Reformulated.AutPerF.Tilt.untilt_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:41.973177+00:00
-- url     : https://prove2.me/theorems/9693da21-52bd-45ce-bed9-d07432eac805
-- title:
--   Tilt: untilt map
-- statement:
--   The Tilt construction uses the untilt map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L123-L135

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
variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

theorem Reformulated.AutPerF.Tilt.untilt_map (f : R →+* S) (x : Tilt p R) :
    PreTilt.untilt (map p f x) = f (PreTilt.untilt x) := by sorry
