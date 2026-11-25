-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_ringKrullDim_int_af7f3029f4b1
-- name    : P2M_GroundTheory_Heights__Heights_le_ringKrullDim_int_af7f3029f4b1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:25.853842+00:00
-- url     : https://prove2.me/theorems/fef7aab3-19f2-4b19-a71a-c88223205021
-- title:
--   P2 M Ground Theory Heights  Heights le ring Krull Dim int af7f3029f4b1: P2 M Ground Theory Heights  Heights le ring Krull Dim int af7f3029f4b1
-- statement:
--   The P2 M Ground Theory Heights  Heights le ring Krull Dim int af7f3029f4b1 construction uses the P2 M Ground Theory Heights  Heights le ring Krull Dim int af7f3029f4b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimBounds.lean#L106-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimBounds.lean#L106-L166

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal
open scoped TensorProduct
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_le_ringKrullDim_int_af7f3029f4b1 (B : Type) [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ) (ht : trdeg ℤ B = t) :
    (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_ringKrullDim_int» := P2M_GroundTheory_Heights__Heights_le_ringKrullDim_int_af7f3029f4b1
