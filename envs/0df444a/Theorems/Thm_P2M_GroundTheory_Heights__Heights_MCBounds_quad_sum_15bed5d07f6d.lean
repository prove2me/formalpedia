-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_sum_15bed5d07f6d
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_sum_15bed5d07f6d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:58.260625+00:00
-- url     : https://prove2.me/theorems/046c9c94-93ba-4ef2-9514-32020fb8ca55
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad sum 15bed5d07f6d: P2 M Ground Theory Heights  Heights MCBounds quad sum 15bed5d07f6d
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad sum 15bed5d07f6d construction uses the P2 M Ground Theory Heights  Heights MCBounds quad sum 15bed5d07f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L42-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_sum_15bed5d07f6d {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ x) = ∑ j ∈ s, x ⬝ᵥ (A j *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_sum» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_sum_15bed5d07f6d
