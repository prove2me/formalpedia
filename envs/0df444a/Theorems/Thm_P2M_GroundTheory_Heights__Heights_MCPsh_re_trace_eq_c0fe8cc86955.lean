-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_re_trace_eq_c0fe8cc86955
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_re_trace_eq_c0fe8cc86955
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:12.250908+00:00
-- url     : https://prove2.me/theorems/6c1d55fe-9e3b-49df-aea1-e8e06cbfedb6
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh re trace eq c0fe8cc86955: P2 M Ground Theory Heights  Heights MCPsh re trace eq c0fe8cc86955
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh re trace eq c0fe8cc86955 construction uses the P2 M Ground Theory Heights  Heights MCPsh re trace eq c0fe8cc86955 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L111-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L111-L126

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_re_trace_eq_c0fe8cc86955 (W : Matrix ι κ ℂ) (Y : Matrix ι ι ℝ) :
    RCLike.re (Wᴴ * cx Y * W).trace =
      ∑ j, ∑ k, (∑ a, (star (W j a) * W k a).re) * Y j k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«re_trace_eq» := P2M_GroundTheory_Heights__Heights_MCPsh_re_trace_eq_c0fe8cc86955
