-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:40.000222+00:00
-- url     : https://prove2.me/theorems/3d08587a-0c70-422c-9ab4-3c95708ce8fd
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh mul Vec injective of rank 78b168dcc192: P2 M Ground Theory Heights  Heights MCPsh mul Vec injective of rank 78b168dcc192
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh mul Vec injective of rank 78b168dcc192 construction uses the P2 M Ground Theory Heights  Heights MCPsh mul Vec injective of rank 78b168dcc192 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L89-L95

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192 {F : Matrix ι κ ℂ} (h : F.rank = Fintype.card κ) :
    Function.Injective F.mulVec := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«mulVec_injective_of_rank» := P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192
