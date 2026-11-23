-- Prove2me | Theorems.Thm_Reformulated_AutPerF_IsPrimitive_padicPow_iff
-- name    : Reformulated.AutPerF.IsPrimitive.padicPow_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:44.242167+00:00
-- url     : https://prove2.me/theorems/cc53e774-d4b1-43c7-a984-485a0215a3b5
-- title:
--   Is Primitive: padic Pow iff
-- statement:
--   The Is Primitive construction uses the padic Pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L210-L216

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

theorem Reformulated.AutPerF.IsPrimitive.padicPow_iff {ε : tateModule p R} (hε : IsPrimitive ε) (a : ℤ_[p]) :
    IsPrimitive (padicPow ε a) ↔ IsUnit a := by sorry
