-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_eq_ofPerfect
-- name    : Reformulated.AutPerF.Tilt.eq_ofPerfect
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:38:08.372488+00:00
-- url     : https://prove2.me/theorems/3270fdf8-5e16-595a-8575-3b51b9c8e117
-- title:
--   Tilt: eq of Perfect
-- statement:
--   The Tilt construction uses the eq of Perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L28-L30

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

theorem Reformulated.AutPerF.Tilt.eq_ofPerfect (f : k →+* R ⧸ span {(p : R)}) (g : k →+* Tilt p R)
    (h : ∀ a, PreTilt.coeff 0 (g a) = f a) : g = Tilt.ofPerfect p f := by sorry
