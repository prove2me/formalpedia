-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_comp_linearIsometry_45b19afbe74f
-- name    : P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_comp_linearIsometry_45b19afbe74f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:48.459906+00:00
-- url     : https://prove2.me/theorems/8231197e-3dae-4461-884f-0b2ce05e65dd
-- title:
--   P2 M Ground Theory Heights  Heights MCGram Entry Deriv comp linear Isometry 45b19afbe74f: P2 M Ground Theory Heights  Heights MCGram Entry Deriv comp linear Isometry 45b19afbe74f
-- statement:
--   The P2 M Ground Theory Heights  Heights MCGram Entry Deriv comp linear Isometry 45b19afbe74f construction uses the P2 M Ground Theory Heights  Heights MCGram Entry Deriv comp linear Isometry 45b19afbe74f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramEntryDeriv.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramEntryDeriv.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv
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
open Matrix
open GroundTheory.Heights₂.Heights.MCGramEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_comp_linearIsometry_45b19afbe74f {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F' →ₗᵢ[ℝ] ℂ) (φ : F' → ℂ) (hφ : ∀ x, L x = φ x) {f : E → F'} {p : E}
    (hf : DifferentiableAt ℝ f p) :
    DifferentiableAt ℝ (fun q => φ (f q)) p ∧
      ‖fderiv ℝ (fun q => φ (f q)) p‖ = ‖fderiv ℝ f p‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCGramEntryDeriv».«comp_linearIsometry» := P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_comp_linearIsometry_45b19afbe74f
