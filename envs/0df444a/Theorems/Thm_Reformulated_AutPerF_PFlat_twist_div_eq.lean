-- Prove2me | Theorems.Thm_Reformulated_AutPerF_PFlat_twist_div_eq
-- name    : Reformulated.AutPerF.PFlat.twist_div_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:08.496393+00:00
-- url     : https://prove2.me/theorems/4f014a0d-4761-5f3f-b4bb-8dbda19df319
-- title:
--   PFlat: twist div eq
-- statement:
--   The PFlat construction uses the twist div eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L404-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L404-L406

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
open Tilt tateModule
open Reformulated.AutPerF.PFlat
variable [IsDomain R] [CharZero R]
variable [ValuationRing R]

theorem Reformulated.AutPerF.PFlat.twist_div_eq (η : tateModule p R) (ϖ' ϖ : PFlat p R) :
    (ϖ'.twist η).div ϖ = η * ϖ'.div ϖ := by sorry
