-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_map_frob
-- name    : Reformulated.AutPerF.AinfInv.map_frob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:19.238893+00:00
-- url     : https://prove2.me/theorems/7bf18f9f-ab16-4b10-8308-64b558cd4745
-- title:
--   Ainf Inv: map frob
-- statement:
--   The Ainf Inv construction uses the map frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L296-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L296-L298

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
open Reformulated.AutPerF.AinfInv
variable {p}

theorem Reformulated.AutPerF.AinfInv.map_frob (f : R →+* S) (x : AinfInv p R) : map p f (frob p R x) = frob p S (map p f x) := by sorry
