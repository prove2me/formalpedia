-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_le_chartRadius_c076bf66d5d4
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_le_chartRadius_c076bf66d5d4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:36.940558+00:00
-- url     : https://prove2.me/theorems/a37cf3b6-d882-48e2-a230-17f2071c9129
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative one le chart Radius c076bf66d5d4: P2 M Ground Theory Heights  Heights Regular Hodge Derivative one le chart Radius c076bf66d5d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative one le chart Radius c076bf66d5d4 construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative one le chart Radius c076bf66d5d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L160-L165

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_le_chartRadius_c076bf66d5d4 {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : 1 ≤ chartRadius h z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«one_le_chartRadius» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_le_chartRadius_c076bf66d5d4
