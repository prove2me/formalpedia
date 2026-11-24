-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:44.866058+00:00
-- url     : https://prove2.me/theorems/5cc930c4-6d74-4083-b3ff-2879e0e81883
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative norm coord lt a42ac747c733: P2 M Ground Theory Heights  Heights Regular Hodge Derivative norm coord lt a42ac747c733
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative norm coord lt a42ac747c733 construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative norm coord lt a42ac747c733 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733 {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (k : Fin n) :
    ‖z k‖ < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«norm_coord_lt» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733
