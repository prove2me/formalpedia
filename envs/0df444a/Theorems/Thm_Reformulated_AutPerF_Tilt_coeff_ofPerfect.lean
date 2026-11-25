-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_coeff_ofPerfect
-- name    : Reformulated.AutPerF.Tilt.coeff_ofPerfect
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:13.101165+00:00
-- url     : https://prove2.me/theorems/8347e457-4e44-4348-a41e-6c72828b54eb
-- title:
--   Tilt: coeff of Perfect
-- statement:
--   The Tilt construction uses the coeff of Perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L24-L25

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

theorem Reformulated.AutPerF.Tilt.coeff_ofPerfect (f : k →+* R ⧸ span {(p : R)}) (n : ℕ) (a : k) :
    PreTilt.coeff n (Tilt.ofPerfect p f a) = f ((frobeniusEquiv k p).symm^[n] a) := by sorry
