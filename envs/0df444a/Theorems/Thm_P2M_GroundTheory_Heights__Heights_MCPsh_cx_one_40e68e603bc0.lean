-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_one_40e68e603bc0
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_cx_one_40e68e603bc0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:36.136965+00:00
-- url     : https://prove2.me/theorems/a3b7c3d6-274c-4257-9785-a1fd3dc903fb
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh cx one 40e68e603bc0: P2 M Ground Theory Heights  Heights MCPsh cx one 40e68e603bc0
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh cx one 40e68e603bc0 construction uses the P2 M Ground Theory Heights  Heights MCPsh cx one 40e68e603bc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L23-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Matrix Metric Real
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem P2M_GroundTheory_Heights__Heights_MCPsh_cx_one_40e68e603bc0 : cx (1 : Matrix ι ι ℝ) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«cx_one» := P2M_GroundTheory_Heights__Heights_MCPsh_cx_one_40e68e603bc0
