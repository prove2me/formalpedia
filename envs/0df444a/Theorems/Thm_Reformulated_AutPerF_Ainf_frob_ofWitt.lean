-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_frob_ofWitt
-- name    : Reformulated.AutPerF.Ainf.frob_ofWitt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:21.048211+00:00
-- url     : https://prove2.me/theorems/81bdade9-3f3e-416b-abaf-995fa2cf2d87
-- title:
--   Ainf: frob of Witt
-- statement:
--   The Ainf construction uses the frob of Witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L48-L51

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

theorem Reformulated.AutPerF.Ainf.frob_ofWitt (f : k →+* R ⧸ span {(p : R)}) (x : WittVector p k) :
    Ainf.frob p R (Ainf.ofWitt p f x) = Ainf.ofWitt p f (WittVector.frobenius x) := by sorry
