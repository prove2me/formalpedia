-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_cuspTime_hasFDerivAt_570f460d4fba
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_cuspTime_hasFDerivAt_570f460d4fba
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:10.658188+00:00
-- url     : https://prove2.me/theorems/06d3927f-0c8f-453b-a26d-04edbbf007c8
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative cusp Time has FDeriv At 570f460d4fba: P2 M Ground Theory Heights  Heights Regular Hodge Derivative cusp Time has FDeriv At 570f460d4fba
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative cusp Time has FDeriv At 570f460d4fba construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative cusp Time has FDeriv At 570f460d4fba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L91-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L91-L120

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

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_cuspTime_hasFDerivAt_570f460d4fba {n a : ℕ} (h : a ≤ n) (i : Fin a) {z : Fin n → ℂ}
    (hz : cuspCoord h z i ≠ 0) :
    ∃ L : (Fin n → ℂ) →L[ℝ] ℝ, HasFDerivAt (fun y => cuspTime h y i) L z ∧
      ‖L‖ ≤ ‖cuspCoord h z i‖⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«cuspTime_hasFDerivAt» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_cuspTime_hasFDerivAt_570f460d4fba
