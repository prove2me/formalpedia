-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_le_trdeg_add_one_int_10c3d154db15
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_le_trdeg_add_one_int_10c3d154db15
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:17.747804+00:00
-- url     : https://prove2.me/theorems/f6dea57a-af99-44c3-bf78-48b27e8918c6
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim le trdeg add one int 10c3d154db15: P2 M Ground Theory Heights  Heights ring Krull Dim le trdeg add one int 10c3d154db15
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim le trdeg add one int 10c3d154db15 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim le trdeg add one int 10c3d154db15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimBounds.lean#L56-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimBounds.lean#L56-L104

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

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_le_trdeg_add_one_int_10c3d154db15 (t : ℕ) : ∀ (B : Type) [CommRing B] [IsDomain B]
    [Algebra ℤ B] [Algebra.FiniteType ℤ B], Function.Injective (algebraMap ℤ B) →
    trdeg ℤ B = t → ringKrullDim B ≤ (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_le_trdeg_add_one_int» := P2M_GroundTheory_Heights__Heights_ringKrullDim_le_trdeg_add_one_int_10c3d154db15
