-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_gram_posDef_60007937f6e3
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_gram_posDef_60007937f6e3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:59.566376+00:00
-- url     : https://prove2.me/theorems/52a1bddb-6bf3-456a-a85e-a15a37afa395
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh gram pos Def 60007937f6e3: P2 M Ground Theory Heights  Heights MCPsh gram pos Def 60007937f6e3
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh gram pos Def 60007937f6e3 construction uses the P2 M Ground Theory Heights  Heights MCPsh gram pos Def 60007937f6e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramContinuous.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramContinuous.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_gram_posDef_60007937f6e3 {g rk : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {F : Matrix (Fin g) (Fin rk) ℂ}
    (hY : Y.PosDef) (hF : F.rank = rk) :
    (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«gram_posDef» := P2M_GroundTheory_Heights__Heights_MCPsh_gram_posDef_60007937f6e3
