-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_eqOn_of_exp_eq_35ecbbb8e43f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_eqOn_of_exp_eq_35ecbbb8e43f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:18.54117+00:00
-- url     : https://prove2.me/theorems/d3f44091-9369-5ec5-b252-ba2f7485e087
-- title:
--   P2 M Ground Theory Heights  Heights Regular eq On of exp eq 35ecbbb8e43f: P2 M Ground Theory Heights  Heights Regular eq On of exp eq 35ecbbb8e43f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular eq On of exp eq 35ecbbb8e43f construction uses the P2 M Ground Theory Heights  Heights Regular eq On of exp eq 35ecbbb8e43f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L75-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_eqOn_of_exp_eq_35ecbbb8e43f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Set E}
    (hW : IsOpen W) (hc : Convex ℝ W) {g₁ g₂ : E → ℂ} (h₁ : ContinuousOn g₁ W)
    (h₂ : ContinuousOn g₂ W) (he : ∀ w ∈ W, Complex.exp (g₁ w) = Complex.exp (g₂ w)) {w₀ : E}
    (hw₀ : w₀ ∈ W) (h₀ : g₁ w₀ = g₂ w₀) : ∀ w ∈ W, g₁ w = g₂ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«eqOn_of_exp_eq» := P2M_GroundTheory_Heights__Heights_Regular_eqOn_of_exp_eq_35ecbbb8e43f
