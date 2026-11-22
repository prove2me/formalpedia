-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_map_frob
-- name    : Reformulated.AutPerF.Ainf.map_frob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:11.100166+00:00
-- url     : https://prove2.me/theorems/d9412e71-7af3-422c-a143-36d5545705b6
-- title:
--   Ainf: map frob
-- statement:
--   The Ainf construction uses the map frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L174-L175

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
open Reformulated.AutPerF.Ainf
variable {p}

theorem Reformulated.AutPerF.Ainf.map_frob (f : R →+* S) (x : Ainf p R) : map p f (frob p R x) = frob p S (map p f x) := by sorry
