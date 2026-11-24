-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:31.910043+00:00
-- url     : https://prove2.me/theorems/399e514a-4a0b-415a-becc-7be298d528f2
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh cx mul 14a24d1b571e: P2 M Ground Theory Heights  Heights MCPsh cx mul 14a24d1b571e
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh cx mul 14a24d1b571e construction uses the P2 M Ground Theory Heights  Heights MCPsh cx mul 14a24d1b571e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L20-L21

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e (Y Z : Matrix ι ι ℝ) : cx (Y * Z) = cx Y * cx Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«cx_mul» := P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e
