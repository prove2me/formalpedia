-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_map_liftWitt
-- name    : Reformulated.AutPerF.Ainf.map_liftWitt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:32.304799+00:00
-- url     : https://prove2.me/theorems/001c3e45-c1c7-4cd4-86bd-12aaa0e63682
-- title:
--   Ainf: map lift Witt
-- statement:
--   The Ainf construction uses the map lift Witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L81-L84

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

theorem Reformulated.AutPerF.Ainf.map_liftWitt (e : R →+* S) (g : WittVector p k →+* R) (x : WittVector p k) :
    Ainf.map p e (Ainf.liftWitt p g x) = Ainf.liftWitt p (e.comp g) x := by sorry
