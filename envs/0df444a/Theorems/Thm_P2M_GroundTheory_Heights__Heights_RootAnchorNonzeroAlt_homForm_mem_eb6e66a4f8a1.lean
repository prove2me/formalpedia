-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_homForm_mem_eb6e66a4f8a1
-- name    : P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_homForm_mem_eb6e66a4f8a1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:34.428342+00:00
-- url     : https://prove2.me/theorems/57374119-de61-4e58-8713-c6fdf230d629
-- title:
--   P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt hom Form mem eb6e66a4f8a1: P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt hom Form mem eb6e66a4f8a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt hom Form mem eb6e66a4f8a1 construction uses the P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt hom Form mem eb6e66a4f8a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L49-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L49-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
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
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt

theorem P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_homForm_mem_eb6e66a4f8a1 {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (q : Polynomial ℤ) (τ : Fin f)
    (I : PlIdx j m) (hq : Polynomial.aeval (rootCoord ζ ⟨τ, I⟩) q = 0) :
    homForm q τ I ∈ rootPointIdeal ζ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootAnchorNonzeroAlt».«homForm_mem» := P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_homForm_mem_eb6e66a4f8a1
