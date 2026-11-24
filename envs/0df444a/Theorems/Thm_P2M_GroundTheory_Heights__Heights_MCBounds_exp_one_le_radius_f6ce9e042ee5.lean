-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exp_one_le_radius_f6ce9e042ee5
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_exp_one_le_radius_f6ce9e042ee5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:49.670869+00:00
-- url     : https://prove2.me/theorems/a141d100-ff73-48c2-ac9c-e37cbcc1f5d3
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds exp one le radius f6ce9e042ee5: P2 M Ground Theory Heights  Heights MCBounds exp one le radius f6ce9e042ee5
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds exp one le radius f6ce9e042ee5 construction uses the P2 M Ground Theory Heights  Heights MCBounds exp one le radius f6ce9e042ee5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L24-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)

theorem P2M_GroundTheory_Heights__Heights_MCBounds_exp_one_le_radius_f6ce9e042ee5 {z : Fin D.n → ℂ} (hz : z ∈ D.U) : Real.exp 1 ≤ D.radius z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«exp_one_le_radius» := P2M_GroundTheory_Heights__Heights_MCBounds_exp_one_le_radius_f6ce9e042ee5
