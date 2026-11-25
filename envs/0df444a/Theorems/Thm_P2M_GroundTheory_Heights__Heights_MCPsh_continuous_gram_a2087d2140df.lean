-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_continuous_gram_a2087d2140df
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_continuous_gram_a2087d2140df
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:19.141492+00:00
-- url     : https://prove2.me/theorems/214674e1-967f-4ef6-bb77-8cd33c41fd1d
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh continuous gram a2087d2140df: P2 M Ground Theory Heights  Heights MCPsh continuous gram a2087d2140df
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh continuous gram a2087d2140df construction uses the P2 M Ground Theory Heights  Heights MCPsh continuous gram a2087d2140df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramContinuous.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramContinuous.lean#L36-L43

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_continuous_gram_a2087d2140df (g rk : ℕ) :
    Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«continuous_gram» := P2M_GroundTheory_Heights__Heights_MCPsh_continuous_gram_a2087d2140df
