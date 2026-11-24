-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb
-- name    : P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:55.872357+00:00
-- url     : https://prove2.me/theorems/fe7a4189-cbd5-4cc1-8942-6eb52cfa19b5
-- title:
--   P2 M Ground Theory Heights  Heights linear Form Line not mem span X0 ace3f4adf1cb: P2 M Ground Theory Heights  Heights linear Form Line not mem span X0 ace3f4adf1cb
-- statement:
--   The P2 M Ground Theory Heights  Heights linear Form Line not mem span X0 ace3f4adf1cb construction uses the P2 M Ground Theory Heights  Heights linear Form Line not mem span X0 ace3f4adf1cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L211-L213

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
open MvPolynomial
noncomputable section
open LineChowForm

theorem P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb : linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linearFormLine_not_mem_span_X0» := P2M_GroundTheory_Heights__Heights_linearFormLine_not_mem_span_X0_ace3f4adf1cb
