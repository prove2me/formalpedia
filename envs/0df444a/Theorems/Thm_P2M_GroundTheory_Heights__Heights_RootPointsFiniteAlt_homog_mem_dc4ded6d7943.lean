-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_mem_dc4ded6d7943
-- name    : P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_mem_dc4ded6d7943
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:03.480551+00:00
-- url     : https://prove2.me/theorems/a407f8f0-1c3e-558d-acc0-e4bcdda141c6
-- title:
--   P2 M Ground Theory Heights  Heights Root Points Finite Alt homog mem dc4ded6d7943: P2 M Ground Theory Heights  Heights Root Points Finite Alt homog mem dc4ded6d7943
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Points Finite Alt homog mem dc4ded6d7943 construction uses the P2 M Ground Theory Heights  Heights Root Points Finite Alt homog mem dc4ded6d7943 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointsFinite.lean#L19-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
variable {K : Type*} {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_mem_dc4ded6d7943 (y : (Σ k, ι k) → ℂ) (k : K) (i i₀ : ι k) (ha : y ⟨k, i₀⟩ = 1) (q : Polynomial ℤ)
    (hq : q.eval₂ (Int.castRingHom ℂ) (y ⟨k, i⟩) = 0) :
    homog q ⟨k, i⟩ ⟨k, i₀⟩ ∈ mCoordIdeal y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointsFiniteAlt».«homog_mem» := P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_mem_dc4ded6d7943
