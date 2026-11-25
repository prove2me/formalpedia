-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_eval__formPoly_18eb8109d79c
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_eval__formPoly_18eb8109d79c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:50.577151+00:00
-- url     : https://prove2.me/theorems/a700ea18-4084-4831-8a08-10944561c232
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points Of Plane eval  form Poly 18eb8109d79c: P2 M Ground Theory Heights  Heights Projective Points Of Plane eval  form Poly 18eb8109d79c
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points Of Plane eval  form Poly 18eb8109d79c construction uses the P2 M Ground Theory Heights  Heights Projective Points Of Plane eval  form Poly 18eb8109d79c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOfPlane.lean#L30-L32

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
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_eval__formPoly_18eb8109d79c (σ : K →+* ℂ) (v : Fin i → ℂ) (p : Σ _ : Unit, ProjIdx K i) :
    eval₂Hom σ v (formPoly p) = projPlanePt σ v p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOfPlane».«eval₂_formPoly» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_eval__formPoly_18eb8109d79c
