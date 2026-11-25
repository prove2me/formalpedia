-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_eq_of_continuousAt_e738391b5387
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_eq_of_continuousAt_e738391b5387
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:25.851788+00:00
-- url     : https://prove2.me/theorems/3c986f74-ea97-4a0c-b6cf-18f1444d7d4f
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad eq of continuous At e738391b5387: P2 M Ground Theory Heights  Heights Regular Exp Quad eq of continuous At e738391b5387
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad eq of continuous At e738391b5387 construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad eq of continuous At e738391b5387 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L16-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L16-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
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
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_eq_of_continuousAt_e738391b5387 {n : ℕ} {F₁ F₂ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (h₁ : ContinuousAt F₁ z) (h₂ : ContinuousAt F₂ z)
    (heq : ∀ y ∈ ball (0 : Fin n → ℂ) 1, (∀ i, y i ≠ 0) → F₁ y = F₂ y) : F₁ z = F₂ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«eq_of_continuousAt» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_eq_of_continuousAt_e738391b5387
