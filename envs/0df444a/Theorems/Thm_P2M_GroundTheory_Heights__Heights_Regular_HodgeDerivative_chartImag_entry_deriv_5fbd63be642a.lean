-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_chartImag_entry_deriv_5fbd63be642a
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_chartImag_entry_deriv_5fbd63be642a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:01.670681+00:00
-- url     : https://prove2.me/theorems/aad5fb15-0a32-4eb4-a369-07bbb1eabf63
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative chart Imag entry deriv 5fbd63be642a: P2 M Ground Theory Heights  Heights Regular Hodge Derivative chart Imag entry deriv 5fbd63be642a
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative chart Imag entry deriv 5fbd63be642a construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative chart Imag entry deriv 5fbd63be642a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L167-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L167-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
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
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_chartImag_entry_deriv_5fbd63be642a {n a g : ℕ} (h : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (p q : Fin g) {z : Fin n → ℂ}
    (hz : ∀ j, cuspCoord h z j ≠ 0) (hT : DifferentiableAt ℝ (fun y => T0 y p q) z) :
    DifferentiableAt ℝ (fun y => chartImag h T0 B y p q) z ∧
      ‖fderiv ℝ (fun y => chartImag h T0 B y p q) z‖ ≤
        ‖fderiv ℝ (fun y => T0 y p q) z‖ + ∑ i, |B i p q| * ‖cuspCoord h z i‖⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«chartImag_entry_deriv» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_chartImag_entry_deriv_5fbd63be642a
