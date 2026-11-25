-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_map_smul_one_sub_741c37bc6f53
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_map_smul_one_sub_741c37bc6f53
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:45.294801+00:00
-- url     : https://prove2.me/theorems/d0eaaa44-cef0-474e-9668-20dc687da2ec
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds map smul one sub 741c37bc6f53: P2 M Ground Theory Heights  Heights MCBounds map smul one sub 741c37bc6f53
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds map smul one sub 741c37bc6f53 construction uses the P2 M Ground Theory Heights  Heights MCBounds map smul one sub 741c37bc6f53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L15-L19

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_map_smul_one_sub_741c37bc6f53 {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (s • (1 : Matrix (Fin g) (Fin g) ℝ) - A).map (fun x : ℝ => (x : ℂ)) =
      (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) - A.map (fun x : ℝ => (x : ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«map_smul_one_sub» := P2M_GroundTheory_Heights__Heights_MCBounds_map_smul_one_sub_741c37bc6f53
