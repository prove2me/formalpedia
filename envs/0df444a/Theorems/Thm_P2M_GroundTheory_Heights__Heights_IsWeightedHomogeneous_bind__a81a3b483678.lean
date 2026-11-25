-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_bind__a81a3b483678
-- name    : P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_bind__a81a3b483678
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:05.113684+00:00
-- url     : https://prove2.me/theorems/b77626aa-74f6-45a3-abec-f5a0d6738d55
-- title:
--   P2 M Ground Theory Heights  Heights Is Weighted Homogeneous bind  a81a3b483678: P2 M Ground Theory Heights  Heights Is Weighted Homogeneous bind  a81a3b483678
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Weighted Homogeneous bind  a81a3b483678 construction uses the P2 M Ground Theory Heights  Heights Is Weighted Homogeneous bind  a81a3b483678 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L31-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L31-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_bind__a81a3b483678 {σ τ : Type*} {w : σ → ℕ} {w' : τ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : σ → MvPolynomial τ R)
    (hφ : ∀ x, IsWeightedHomogeneous w' (φ x) (w x)) :
    IsWeightedHomogeneous w' (bind₁ φ f) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsWeightedHomogeneous».«bind₁» := P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_bind__a81a3b483678
