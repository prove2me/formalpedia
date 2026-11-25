-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_seq_eq_untilt
-- name    : Reformulated.AutPerF.Tilt.seq_eq_untilt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:38:38.357707+00:00
-- url     : https://prove2.me/theorems/ff72d1d1-eb2d-4ce9-b658-38957cde9646
-- title:
--   Tilt: seq eq untilt
-- statement:
--   The Tilt construction uses the seq eq untilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L63-L67

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
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
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Reformulated.AutPerF.Tilt

theorem Reformulated.AutPerF.Tilt.seq_eq_untilt (y : Tilt p R) (n : ℕ) :
    seq n y = PreTilt.untilt (((frobeniusEquiv (Tilt p R) p).symm)^[n] y) := by sorry
