-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_map_ofPerfect
-- name    : Reformulated.AutPerF.Tilt.map_ofPerfect
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:54.480122+00:00
-- url     : https://prove2.me/theorems/9c7a4a3e-77fa-4238-ba89-556035630a2e
-- title:
--   Tilt: map of Perfect
-- statement:
--   The Tilt construction uses the map of Perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L33-L36

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
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.Tilt.map_ofPerfect (e : R →+* S) (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Tilt.map p e (Tilt.ofPerfect p f a) =
      Tilt.ofPerfect p ((Ideal.quotientMap _ e (span_natCast_le_comap p e)).comp f) a := by sorry
