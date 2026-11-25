-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_lin_eq_3c8f669433de
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_lin_eq_3c8f669433de
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:47.656259+00:00
-- url     : https://prove2.me/theorems/1a1596c8-440d-4e8d-b05c-a3424065cb9b
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane lin eq 3c8f669433de: P2 M Ground Theory Heights  Heights Projective Points On Plane lin eq 3c8f669433de
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane lin eq 3c8f669433de construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane lin eq 3c8f669433de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L53-L69

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

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_lin_eq_3c8f669433de (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (q : ProjIdx K i) :
    lin α Z q = ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (σ (α : K) * embComp σ Z q.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«lin_eq» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_lin_eq_3c8f669433de
