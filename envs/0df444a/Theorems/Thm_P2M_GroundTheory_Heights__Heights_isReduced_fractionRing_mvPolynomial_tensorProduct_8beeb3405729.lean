-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_fractionRing_mvPolynomial_tensorProduct_8beeb3405729
-- name    : P2M_GroundTheory_Heights__Heights_isReduced_fractionRing_mvPolynomial_tensorProduct_8beeb3405729
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:24.142736+00:00
-- url     : https://prove2.me/theorems/3a297b06-5f15-4670-a851-b89089fc74b7
-- title:
--   P2 M Ground Theory Heights  Heights is Reduced fraction Ring mv Polynomial tensor Product 8beeb3405729: P2 M Ground Theory Heights  Heights is Reduced fraction Ring mv Polynomial tensor Product 8beeb3
-- statement:
--   The P2 M Ground Theory Heights  Heights is Reduced fraction Ring mv Polynomial tensor Product 8beeb3405729 construction uses the P2 M Ground Theory Heights  Heights is Reduced fraction Ring mv Polynomial tensor Product 8beeb3405729 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L59-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L59-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
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
open TensorProduct
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_isReduced_fractionRing_mvPolynomial_tensorProduct_8beeb3405729 (K : Type u) [Field K] (σ : Type u)
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (FractionRing (MvPolynomial σ K) ⊗[K] L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isReduced_fractionRing_mvPolynomial_tensorProduct» := P2M_GroundTheory_Heights__Heights_isReduced_fractionRing_mvPolynomial_tensorProduct_8beeb3405729
