-- Prove2me | Theorems.Thm_Reformulated_AutPerF_tateModule_map_eq_padicPow_cyclotomicCharacter
-- name    : Reformulated.AutPerF.tateModule.map_eq_padicPow_cyclotomicCharacter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:31.047342+00:00
-- url     : https://prove2.me/theorems/932e87a3-5993-42c0-ac2f-f4dba1c6ec27
-- title:
--   tate Module: map eq padic Pow cyclotomic Character
-- statement:
--   The tate Module construction uses the map eq padic Pow cyclotomic Character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L332-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L332-L337

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
variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]
variable [CharZero R]

theorem Reformulated.AutPerF.tateModule.map_eq_padicPow_cyclotomicCharacter (e : R ≃+* R) (η : tateModule p R) :
    Tilt.map p (e : R →+* R) η.1 = (padicPow η (cyclotomicCharacter R p e)).1 := by sorry
