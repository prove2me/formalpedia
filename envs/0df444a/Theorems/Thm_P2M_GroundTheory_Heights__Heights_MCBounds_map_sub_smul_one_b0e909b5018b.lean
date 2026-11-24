-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_map_sub_smul_one_b0e909b5018b
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_map_sub_smul_one_b0e909b5018b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:03.852208+00:00
-- url     : https://prove2.me/theorems/fe700c1d-ab92-4f4c-a8a9-4664cefed871
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds map sub smul one b0e909b5018b: P2 M Ground Theory Heights  Heights MCBounds map sub smul one b0e909b5018b
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds map sub smul one b0e909b5018b construction uses the P2 M Ground Theory Heights  Heights MCBounds map sub smul one b0e909b5018b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix MCBounds
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_map_sub_smul_one_b0e909b5018b {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (A - s • (1 : Matrix (Fin g) (Fin g) ℝ)).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) - (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«map_sub_smul_one» := P2M_GroundTheory_Heights__Heights_MCBounds_map_sub_smul_one_b0e909b5018b
