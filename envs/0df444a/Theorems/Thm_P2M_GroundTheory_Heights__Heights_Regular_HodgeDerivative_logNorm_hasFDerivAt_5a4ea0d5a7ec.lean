-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logNorm_hasFDerivAt_5a4ea0d5a7ec
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logNorm_hasFDerivAt_5a4ea0d5a7ec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:57.748664+00:00
-- url     : https://prove2.me/theorems/99092fc0-2cbe-43e5-823d-d72b3b34265b
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Norm has FDeriv At 5a4ea0d5a7ec: P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Norm has FDeriv At 5a4ea0d5a7ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Norm has FDeriv At 5a4ea0d5a7ec construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Norm has FDeriv At 5a4ea0d5a7ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L72-L89

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logNorm_hasFDerivAt_5a4ea0d5a7ec {x : ℂ} (hx : x ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun y : ℂ => Real.log ‖y‖) L x ∧ ‖L‖ ≤ ‖x‖⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«logNorm_hasFDerivAt» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logNorm_hasFDerivAt_5a4ea0d5a7ec
