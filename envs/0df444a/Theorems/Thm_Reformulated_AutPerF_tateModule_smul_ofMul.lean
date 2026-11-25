-- Prove2me | Theorems.Thm_Reformulated_AutPerF_tateModule_smul_ofMul
-- name    : Reformulated.AutPerF.tateModule.smul_ofMul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:59.189796+00:00
-- url     : https://prove2.me/theorems/9db24b4b-62f9-4232-b91c-a34b2da4da4f
-- title:
--   tate Module: smul of Mul
-- statement:
--   The tate Module construction uses the smul of Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L169-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L169-L170

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
open Reformulated.AutPerF.tateModule
open Tilt

theorem Reformulated.AutPerF.tateModule.smul_ofMul (a : ℤ_[p]) (η : tateModule p R) :
    a • Additive.ofMul η = Additive.ofMul (padicPow η a) := by sorry
