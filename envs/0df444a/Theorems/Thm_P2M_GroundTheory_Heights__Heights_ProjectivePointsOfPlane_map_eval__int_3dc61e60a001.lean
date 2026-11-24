-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:59.115553+00:00
-- url     : https://prove2.me/theorems/12a58aee-c0da-48dd-8436-d3bba61a3863
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points Of Plane map eval  int 3dc61e60a001: P2 M Ground Theory Heights  Heights Projective Points Of Plane map eval  int 3dc61e60a001
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points Of Plane map eval  int 3dc61e60a001 construction uses the P2 M Ground Theory Heights  Heights Projective Points Of Plane map eval  int 3dc61e60a001 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean#L13-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane
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
open GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001 {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOfPlane».«map_eval₂_int» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_eval__int_3dc61e60a001
