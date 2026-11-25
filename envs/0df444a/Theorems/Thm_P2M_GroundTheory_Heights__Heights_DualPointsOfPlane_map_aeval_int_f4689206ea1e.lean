-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_aeval_int_f4689206ea1e
-- name    : P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_aeval_int_f4689206ea1e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:54.46319+00:00
-- url     : https://prove2.me/theorems/6d9eb2d9-3388-5481-a893-10374befd8c9
-- title:
--   P2 M Ground Theory Heights  Heights Dual Points Of Plane map aeval int f4689206ea1e: P2 M Ground Theory Heights  Heights Dual Points Of Plane map aeval int f4689206ea1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Points Of Plane map aeval int f4689206ea1e construction uses the P2 M Ground Theory Heights  Heights Dual Points Of Plane map aeval int f4689206ea1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualPtsOfPlane.lean#L20-L23

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

theorem P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_aeval_int_f4689206ea1e {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualPointsOfPlane».«map_aeval_int» := P2M_GroundTheory_Heights__Heights_DualPointsOfPlane_map_aeval_int_f4689206ea1e
