-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_quad_mem_0cdb3f18228b
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_quad_mem_0cdb3f18228b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:22:27.516928+00:00
-- url     : https://prove2.me/theorems/d9778111-1cdf-502c-8b00-f959ef597877
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane quad mem 0cdb3f18228b: P2 M Ground Theory Heights  Heights Projective Points On Plane quad mem 0cdb3f18228b
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane quad mem 0cdb3f18228b construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane quad mem 0cdb3f18228b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L85-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L85-L110

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

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_quad_mem_0cdb3f18228b (α : 𝓞 K) (p q : ProjIdx K i) : quad α p q ∈ projSpaceIdeal K i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«quad_mem» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_quad_mem_0cdb3f18228b
