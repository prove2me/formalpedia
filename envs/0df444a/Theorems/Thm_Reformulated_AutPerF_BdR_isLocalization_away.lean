-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdR_isLocalization_away
-- name    : Reformulated.AutPerF.BdR.isLocalization_away
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:20.886619+00:00
-- url     : https://prove2.me/theorems/8663b126-e164-4a8b-a7c7-2d236f395abb
-- title:
--   Bd R: is Localization away
-- statement:
--   The Bd R construction uses the is Localization away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L302-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L302-L315

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
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
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdR
variable [IsAlgClosed (FractionRing R)]
variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ

theorem Reformulated.AutPerF.BdR.isLocalization_away : IsLocalization.Away π (BdR p R) := by sorry
