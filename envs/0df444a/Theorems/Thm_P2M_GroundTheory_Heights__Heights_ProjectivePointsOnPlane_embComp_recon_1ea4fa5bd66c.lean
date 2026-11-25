-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_recon_1ea4fa5bd66c
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_recon_1ea4fa5bd66c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:58.33622+00:00
-- url     : https://prove2.me/theorems/fa287645-9c01-4bd7-8c50-098c70eee2e0
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp recon 1ea4fa5bd66c: P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp recon 1ea4fa5bd66c
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp recon 1ea4fa5bd66c construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane emb Comp recon 1ea4fa5bd66c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L27-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L27-L48

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
open scoped Classical

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_recon_1ea4fa5bd66c (u : (K →+* ℂ) → Fin i → ℂ) (τ : K →+* ℂ) :
    embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) = u τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«embComp_recon» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_recon_1ea4fa5bd66c
