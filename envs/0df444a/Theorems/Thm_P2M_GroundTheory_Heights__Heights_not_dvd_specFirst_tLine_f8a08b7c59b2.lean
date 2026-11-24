-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2
-- name    : P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:15.086783+00:00
-- url     : https://prove2.me/theorems/0617ea2b-8eaf-4e9a-ad9a-b12d743a8be1
-- title:
--   P2 M Ground Theory Heights  Heights not dvd spec First t Line f8a08b7c59b2: P2 M Ground Theory Heights  Heights not dvd spec First t Line f8a08b7c59b2
-- statement:
--   The P2 M Ground Theory Heights  Heights not dvd spec First t Line f8a08b7c59b2 construction uses the P2 M Ground Theory Heights  Heights not dvd spec First t Line f8a08b7c59b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L192-L195

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

theorem P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2 :
    ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine := by sorry

alias «GroundTheory».«Heights₂».«Heights».«not_dvd_specFirst_tLine» := P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2
