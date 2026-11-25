-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_map_liftFracWitt
-- name    : Reformulated.AutPerF.AinfInv.map_liftFracWitt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:09.453644+00:00
-- url     : https://prove2.me/theorems/9f89fcda-b7bd-44d7-9b51-eb3fe72cfc3e
-- title:
--   Ainf Inv: map lift Frac Witt
-- statement:
--   The Ainf Inv construction uses the map lift Frac Witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L152-L156

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
variable {p}

theorem Reformulated.AutPerF.AinfInv.map_liftFracWitt (e : R →+* S) (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    AinfInv.map p e (AinfInv.liftFracWitt p g x) = AinfInv.liftFracWitt p (e.comp g) x := by sorry
