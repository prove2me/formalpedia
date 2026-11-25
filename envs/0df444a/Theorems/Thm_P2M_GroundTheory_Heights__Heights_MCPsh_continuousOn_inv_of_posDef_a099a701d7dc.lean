-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_continuousOn_inv_of_posDef_a099a701d7dc
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_continuousOn_inv_of_posDef_a099a701d7dc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:18.026038+00:00
-- url     : https://prove2.me/theorems/0a52c07c-2336-4927-a085-6d498760d8ed
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh continuous On inv of pos Def a099a701d7dc: P2 M Ground Theory Heights  Heights MCPsh continuous On inv of pos Def a099a701d7dc
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh continuous On inv of pos Def a099a701d7dc construction uses the P2 M Ground Theory Heights  Heights MCPsh continuous On inv of pos Def a099a701d7dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramContinuous.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramContinuous.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramContinuous
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
open Matrix Metric MCPsh
open scoped MatrixOrder ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.MCPsh

theorem P2M_GroundTheory_Heights__Heights_MCPsh_continuousOn_inv_of_posDef_a099a701d7dc {X : Type} [TopologicalSpace X] {s : Set X} {g : ℕ}
    {Y : X → Matrix (Fin g) (Fin g) ℝ} (hY : ContinuousOn Y s) (hpd : ∀ x ∈ s, (Y x).PosDef) :
    ContinuousOn (fun x => (Y x)⁻¹) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«continuousOn_inv_of_posDef» := P2M_GroundTheory_Heights__Heights_MCPsh_continuousOn_inv_of_posDef_a099a701d7dc
