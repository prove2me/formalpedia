-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_aeval_int_01a6887550a7
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_aeval_int_01a6887550a7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:25.818437+00:00
-- url     : https://prove2.me/theorems/3a63ca95-b4cf-4c4e-bc56-3ee2a2a5f76e
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points Of Plane map aeval int 01a6887550a7: P2 M Ground Theory Heights  Heights Projective Points Of Plane map aeval int 01a6887550a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points Of Plane map aeval int 01a6887550a7 construction uses the P2 M Ground Theory Heights  Heights Projective Points Of Plane map aeval int 01a6887550a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean#L20-L23

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

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_aeval_int_01a6887550a7 {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOfPlane».«map_aeval_int» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_map_aeval_int_01a6887550a7
