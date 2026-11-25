-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_not_unit_of_pow_succ_d05b5f3dd358
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_not_unit_of_pow_succ_d05b5f3dd358
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:27.337558+00:00
-- url     : https://prove2.me/theorems/3cb7c130-d352-413d-9a0a-cfc9520ac8bd
-- title:
--   P2 M Ground Theory Heights  Heights Vertical not unit of pow succ d05b5f3dd358: P2 M Ground Theory Heights  Heights Vertical not unit of pow succ d05b5f3dd358
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical not unit of pow succ d05b5f3dd358 construction uses the P2 M Ground Theory Heights  Heights Vertical not unit of pow succ d05b5f3dd358 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PPrimitiveUnit.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PPrimitiveUnit.lean#L11-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PPrimitiveUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_not_unit_of_pow_succ_d05b5f3dd358 {R : Type*} [CommRing R] [IsDomain R] {ϖ : R} (hϖ : Irreducible ϖ)
    (u₁ u₂ : Rˣ) (i d : ℕ) {x y : R} (hy : IsUnit y)
    (h : (u₂ : R) * ϖ ^ (i + d + 1) * x = u₁ * ϖ ^ i * y) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«not_unit_of_pow_succ» := P2M_GroundTheory_Heights__Heights_Vertical_not_unit_of_pow_succ_d05b5f3dd358
