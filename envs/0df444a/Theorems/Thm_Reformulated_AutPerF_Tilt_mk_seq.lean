-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_mk_seq
-- name    : Reformulated.AutPerF.Tilt.mk_seq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:30.382343+00:00
-- url     : https://prove2.me/theorems/d3e66e4f-3475-4c1d-97c6-1bf19954f443
-- title:
--   Tilt: mk seq
-- statement:
--   The Tilt construction uses the mk seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L53-L57

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

theorem Reformulated.AutPerF.Tilt.mk_seq (y : Tilt p R) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : R)}) (seq n y) = PreTilt.coeff n y := by sorry
