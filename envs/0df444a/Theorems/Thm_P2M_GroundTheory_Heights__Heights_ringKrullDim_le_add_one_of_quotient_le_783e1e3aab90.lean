-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_le_add_one_of_quotient_le_783e1e3aab90
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_le_add_one_of_quotient_le_783e1e3aab90
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:20.275784+00:00
-- url     : https://prove2.me/theorems/545804b3-432f-4c82-8463-7e4a8e6ad4f9
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim le add one of quotient le 783e1e3aab90: P2 M Ground Theory Heights  Heights ring Krull Dim le add one of quotient le 783e1e3aab90
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim le add one of quotient le 783e1e3aab90 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim le add one of quotient le 783e1e3aab90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimBounds.lean#L32-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimBounds.lean#L32-L54

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

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_le_add_one_of_quotient_le_783e1e3aab90 {B : Type} [CommRing B] [IsDomain B] (n : ℕ∞)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → ringKrullDim (B ⧸ Q) ≤ n) :
    ringKrullDim B ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_le_add_one_of_quotient_le» := P2M_GroundTheory_Heights__Heights_ringKrullDim_le_add_one_of_quotient_le_783e1e3aab90
