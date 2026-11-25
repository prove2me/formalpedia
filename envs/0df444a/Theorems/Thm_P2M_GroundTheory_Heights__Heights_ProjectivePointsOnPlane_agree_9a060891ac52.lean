-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_agree_9a060891ac52
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_agree_9a060891ac52
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:30.844746+00:00
-- url     : https://prove2.me/theorems/034346b2-7203-4437-ba83-638df5901639
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane agree 9a060891ac52: P2 M Ground Theory Heights  Heights Projective Points On Plane agree 9a060891ac52
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane agree 9a060891ac52 construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane agree 9a060891ac52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L117-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L117-L138

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

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_agree_9a060891ac52 (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (hz : z ∈ mcPts (projSpaceIdeal K i)) (α : 𝓞 K)
    (σ τ : K →+* ℂ) (j l : Fin i) (hσ : embComp σ (fun q => z ⟨(), q⟩) j ≠ 0)
    (hτ : embComp τ (fun q => z ⟨(), q⟩) l ≠ 0) : σ (α : K) = τ (α : K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«agree» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_agree_9a060891ac52
