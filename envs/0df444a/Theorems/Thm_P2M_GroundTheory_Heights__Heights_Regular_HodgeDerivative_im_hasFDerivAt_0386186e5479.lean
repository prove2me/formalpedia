-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_im_hasFDerivAt_0386186e5479
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_im_hasFDerivAt_0386186e5479
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:05.951137+00:00
-- url     : https://prove2.me/theorems/8d7496a7-4904-4e1a-8338-7734347d13ec
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative im has FDeriv At 0386186e5479: P2 M Ground Theory Heights  Heights Regular Hodge Derivative im has FDeriv At 0386186e5479
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative im has FDeriv At 0386186e5479 construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative im has FDeriv At 0386186e5479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L122-L129

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_im_hasFDerivAt_0386186e5479 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x ∧
      ‖Complex.imCLM.comp (fderiv ℝ f x)‖ ≤ ‖fderiv ℝ f x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«im_hasFDerivAt» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_im_hasFDerivAt_0386186e5479
