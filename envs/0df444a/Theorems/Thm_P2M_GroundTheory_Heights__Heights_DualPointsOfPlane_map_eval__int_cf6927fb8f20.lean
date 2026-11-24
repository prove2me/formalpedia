-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:45.627679+00:00
-- url     : https://prove2.me/theorems/731d4cc4-0855-41b8-b6ac-88a299fdd554
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points Of Plane map eval  int cf6927fb8f20: P2 M Ground Theory Heights  Heights Dual Points Of Plane map eval  int cf6927fb8f20
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points Of Plane map eval  int cf6927fb8f20 construction uses the P2 M Ground Theory Heights  Heights Dual Points Of Plane map eval  int cf6927fb8f20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualPointsOfPlane

theorem P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20 {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOfPlane».«map_eval₂_int» := P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_eval__int_cf6927fb8f20
