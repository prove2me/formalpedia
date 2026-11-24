-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:21.793345+00:00
-- url     : https://prove2.me/theorems/7ab142b5-f074-4364-a946-61e302b1571a
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative exp Cover log Lift 06dd0ae602f8: P2 M Ground Theory Heights  Heights Regular Hodge Derivative exp Cover log Lift 06dd0ae602f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative exp Cover log Lift 06dd0ae602f8 construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative exp Cover log Lift 06dd0ae602f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L41-L50

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8 {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ} (hz : ∀ j, cuspCoord h z j ≠ 0) :
    expCover a (logLift a z) = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«expCover_logLift» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8
