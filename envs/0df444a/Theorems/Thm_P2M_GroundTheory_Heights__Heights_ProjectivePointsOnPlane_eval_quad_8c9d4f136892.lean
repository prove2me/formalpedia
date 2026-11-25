-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_eval_quad_8c9d4f136892
-- name    : P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_eval_quad_8c9d4f136892
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:01.580254+00:00
-- url     : https://prove2.me/theorems/f6ef2827-e0db-592c-8124-9f48288fb68a
-- title:
--   P2 M Ground Theory Heights  Heights Projective Points On Plane eval quad 8c9d4f136892: P2 M Ground Theory Heights  Heights Projective Points On Plane eval quad 8c9d4f136892
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Points On Plane eval quad 8c9d4f136892 construction uses the P2 M Ground Theory Heights  Heights Projective Points On Plane eval quad 8c9d4f136892 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean#L112-L115

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

theorem P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_eval_quad_8c9d4f136892 (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (α : 𝓞 K) (p q : ProjIdx K i) :
    eval z (map (Int.castRingHom ℂ) (quad α p q)) =
      z ⟨(), p⟩ * lin α (fun r => z ⟨(), r⟩) q - lin α (fun r => z ⟨(), r⟩) p * z ⟨(), q⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectivePointsOnPlane».«eval_quad» := P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_eval_quad_8c9d4f136892
