-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_qLine_mem_incIdeal_b37e658e70cf
-- name    : P2M_GroundTheory_Heights__Heights_qLine_mem_incIdeal_b37e658e70cf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:36.313424+00:00
-- url     : https://prove2.me/theorems/8da65fe1-7280-4c77-8bb7-a0c5af73991d
-- title:
--   P2 M Ground Theory Heights  Heights q Line mem inc Ideal b37e658e70cf: P2 M Ground Theory Heights  Heights q Line mem inc Ideal b37e658e70cf
-- statement:
--   The P2 M Ground Theory Heights  Heights q Line mem inc Ideal b37e658e70cf construction uses the P2 M Ground Theory Heights  Heights q Line mem inc Ideal b37e658e70cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L202-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L202-L209

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

theorem P2M_GroundTheory_Heights__Heights_qLine_mem_incIdeal_b37e658e70cf : qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«qLine_mem_incIdeal» := P2M_GroundTheory_Heights__Heights_qLine_mem_incIdeal_b37e658e70cf
