-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirst_tLine_not_mem_ccadebe4d4f7
-- name    : P2M_GroundTheory_Heights__Heights_specFirst_tLine_not_mem_ccadebe4d4f7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:29.575009+00:00
-- url     : https://prove2.me/theorems/d833331e-db34-4123-b8ea-1594cf6e778f
-- title:
--   P2 M Ground Theory Heights  Heights spec First t Line not mem ccadebe4d4f7: P2 M Ground Theory Heights  Heights spec First t Line not mem ccadebe4d4f7
-- statement:
--   The P2 M Ground Theory Heights  Heights spec First t Line not mem ccadebe4d4f7 construction uses the P2 M Ground Theory Heights  Heights spec First t Line not mem ccadebe4d4f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L197-L200

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

theorem P2M_GroundTheory_Heights__Heights_specFirst_tLine_not_mem_ccadebe4d4f7 :
    specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine ∉ Ideal.span {qLine} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«specFirst_tLine_not_mem» := P2M_GroundTheory_Heights__Heights_specFirst_tLine_not_mem_ccadebe4d4f7
