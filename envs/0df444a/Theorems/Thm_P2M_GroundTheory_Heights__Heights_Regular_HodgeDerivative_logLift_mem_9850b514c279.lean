-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:30.222139+00:00
-- url     : https://prove2.me/theorems/714ebce1-3ef8-4628-949f-63a3cf5a9920
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Lift mem 9850b514c279: P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Lift mem 9850b514c279
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Lift mem 9850b514c279 construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative log Lift mem 9850b514c279 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L31-L39

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279 {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : logLift a z ∈ logCover h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«logLift_mem» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279
