-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:32.963208+00:00
-- url     : https://prove2.me/theorems/0548d73c-45bb-433a-8b74-9e29c7ec346b
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh cx pos Def f752d4d37fd2: P2 M Ground Theory Heights  Heights MCPsh cx pos Def f752d4d37fd2
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh cx pos Def f752d4d37fd2 construction uses the P2 M Ground Theory Heights  Heights MCPsh cx pos Def f752d4d37fd2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L29-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L29-L79

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2 {Y : Matrix ι ι ℝ} (hY : Y.PosDef) : (cx Y).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«cx_posDef» := P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2
