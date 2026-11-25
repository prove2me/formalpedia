-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplGcd_of_gcd_ne_zero_6e1d1ea73b66
-- name    : P2M_GroundTheory_Heights__Heights_PSymplGcd_of_gcd_ne_zero_6e1d1ea73b66
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:12.455567+00:00
-- url     : https://prove2.me/theorems/7efbded1-09c6-457c-9f0b-88b4b3e8cd4f
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Gcd of gcd ne zero 6e1d1ea73b66: P2 M Ground Theory Heights  Heights PSympl Gcd of gcd ne zero 6e1d1ea73b66
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Gcd of gcd ne zero 6e1d1ea73b66 construction uses the P2 M Ground Theory Heights  Heights PSympl Gcd of gcd ne zero 6e1d1ea73b66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplGcd.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplGcd.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplGcd
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
open GroundTheory.Heights₂.Heights.PSymplGcd

theorem P2M_GroundTheory_Heights__Heights_PSymplGcd_of_gcd_ne_zero_6e1d1ea73b66 (a b : ℤ) (hc : (Int.gcd a b : ℤ) ≠ 0) :
    ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplGcd».«of_gcd_ne_zero» := P2M_GroundTheory_Heights__Heights_PSymplGcd_of_gcd_ne_zero_6e1d1ea73b66
