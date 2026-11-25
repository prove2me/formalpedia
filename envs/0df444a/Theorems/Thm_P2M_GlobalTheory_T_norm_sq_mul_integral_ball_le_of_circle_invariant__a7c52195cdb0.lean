-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_norm_sq_mul_integral_ball_le_of_circle_invariant__a7c52195cdb0
-- name    : P2M_GlobalTheory_T_norm_sq_mul_integral_ball_le_of_circle_invariant__a7c52195cdb0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:15.978075+00:00
-- url     : https://prove2.me/theorems/abfb66c5-c794-4a98-b633-b20fdca4aef6
-- title:
--   P2 M Global Theory T norm sq mul integral ball le of circle invariant  a7c52195cdb0: P2 M Global Theory T norm sq mul integral ball le of circle invariant  a7c52195cdb0
-- statement:
--   The P2 M Global Theory T norm sq mul integral ball le of circle invariant  a7c52195cdb0 construction uses the P2 M Global Theory T norm sq mul integral ball le of circle invariant  a7c52195cdb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormSqMulIntegralBallLeOfCircleInvariantStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormSqMulIntegralBallLeOfCircleInvariantStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariant
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_norm_sq_mul_integral_ball_le_of_circle_invariant__a7c52195cdb0 : ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U → closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) → (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) → ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by sorry

alias «GlobalTheory».«T».«norm_sq_mul_integral_ball_le_of_circle_invariant'» := P2M_GlobalTheory_T_norm_sq_mul_integral_ball_le_of_circle_invariant__a7c52195cdb0
