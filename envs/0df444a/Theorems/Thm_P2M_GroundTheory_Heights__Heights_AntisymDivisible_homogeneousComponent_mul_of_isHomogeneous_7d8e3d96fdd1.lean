-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_homogeneousComponent_mul_of_isHomogeneous_7d8e3d96fdd1
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_homogeneousComponent_mul_of_isHomogeneous_7d8e3d96fdd1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:44.299501+00:00
-- url     : https://prove2.me/theorems/cb664468-3f10-40d5-8708-3928c41d3814
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible homogeneous Component mul of is Homogeneous 7d8e3d96fdd1: P2 M Ground Theory Heights  Heights Antisym Divisible homogeneous Component mul of is Ho
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible homogeneous Component mul of is Homogeneous 7d8e3d96fdd1 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible homogeneous Component mul of is Homogeneous 7d8e3d96fdd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L152-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L152-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_homogeneousComponent_mul_of_isHomogeneous_7d8e3d96fdd1 {Δ : MvPolynomial σ ℝ} {D : ℕ}
    (hΔ : Δ.IsHomogeneous D) (l : MvPolynomial σ ℝ) (n : ℕ) :
    homogeneousComponent (D + n) (Δ * l) = Δ * homogeneousComponent n l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«homogeneousComponent_mul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_homogeneousComponent_mul_of_isHomogeneous_7d8e3d96fdd1
