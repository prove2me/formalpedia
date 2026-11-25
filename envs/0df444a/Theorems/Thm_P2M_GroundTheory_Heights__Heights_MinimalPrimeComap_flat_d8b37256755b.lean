-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_flat_d8b37256755b
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_flat_d8b37256755b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:12.804992+00:00
-- url     : https://prove2.me/theorems/80105e53-c286-40c2-a8b7-6482a8dc0dec
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Comap flat d8b37256755b: P2 M Ground Theory Heights  Heights Minimal Prime Comap flat d8b37256755b
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Comap flat d8b37256755b construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Comap flat d8b37256755b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMinimalPrimeComap.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMinimalPrimeComap.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMinimalPrimeComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_flat_d8b37256755b (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    let := σ.toAlgebra
    let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimeComap».«flat» := P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_flat_d8b37256755b
