-- Prove2me | Theorems.Thm_Reformulated_AutPerF_isPrimitive_eps
-- name    : Reformulated.AutPerF.isPrimitive_eps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:15.592683+00:00
-- url     : https://prove2.me/theorems/634e98ff-315c-4671-955e-e8bbfa44c013
-- title:
--   Aut Per F: is Primitive eps
-- statement:
--   The Aut Per F construction uses the is Primitive eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L330-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L330-L330

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
variable (p R)

theorem Reformulated.AutPerF.isPrimitive_eps : IsPrimitive (eps p R) := by sorry
