-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_map_ofWitt
-- name    : Reformulated.AutPerF.Ainf.map_ofWitt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:15.443319+00:00
-- url     : https://prove2.me/theorems/66292a31-8890-4c0b-8ad8-6bee725774db
-- title:
--   Ainf: map of Witt
-- statement:
--   The Ainf construction uses the map of Witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L55-L59

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

theorem Reformulated.AutPerF.Ainf.map_ofWitt (e : R →+* S) (f : k →+* R ⧸ span {(p : R)}) (x : WittVector p k) :
    Ainf.map p e (Ainf.ofWitt p f x) =
      Ainf.ofWitt p ((Ideal.quotientMap _ e (span_natCast_le_comap p e)).comp f) x := by sorry
