-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_lin_2d6da04684f4
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_lin_2d6da04684f4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:12.37589+00:00
-- url     : https://prove2.me/theorems/a5df4aee-3127-4372-b8a1-2ab71fa73bd9
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp lin 2d6da04684f4: P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp lin 2d6da04684f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp lin 2d6da04684f4 construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp lin 2d6da04684f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L71-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
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
open GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_lin_2d6da04684f4 (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (τ : K →+* ℂ) :
    embComp τ (lin α Z) = τ (α : K) • embComp τ Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«embComp_lin» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_lin_2d6da04684f4
