-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:46.246689+00:00
-- url     : https://prove2.me/theorems/e5e12df3-0b88-4814-9408-2737ad52cb6c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mul form f630f1747419: P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mul form f630f17474
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mul form f630f1747419 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mul form f630f1747419 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
open Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419 {x y : MRing ι R} {j : K → ℕ}
    (hy : IsMultiHomog y j) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (x * y) =
      if j ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - j) x * y else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weightedHomogeneousComponent_mul_form» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mul_form_f630f1747419
