-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProductFormula_prod_norm_embeddings_5b2a354076b7
-- name    : P2M_GroundTheory_Heights__Heights_KLinesProductFormula_prod_norm_embeddings_5b2a354076b7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:39.728828+00:00
-- url     : https://prove2.me/theorems/eff3b951-f76c-550f-b86c-a11ec09e3056
-- title:
--   P2 M Ground Theory Heights  Heights KLines Product Formula prod norm embeddings 5b2a354076b7: P2 M Ground Theory Heights  Heights KLines Product Formula prod norm embeddings 5b2a354076b7
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Product Formula prod norm embeddings 5b2a354076b7 construction uses the P2 M Ground Theory Heights  Heights KLines Product Formula prod norm embeddings 5b2a354076b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProductFormula.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProductFormula.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProductFormula
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
open NumberField
open GroundTheory.Heights₂.Heights.KLinesProductFormula

theorem P2M_GroundTheory_Heights__Heights_KLinesProductFormula_prod_norm_embeddings_5b2a354076b7 (K : Type) [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesProductFormula».«prod_norm_embeddings» := P2M_GroundTheory_Heights__Heights_KLinesProductFormula_prod_norm_embeddings_5b2a354076b7
