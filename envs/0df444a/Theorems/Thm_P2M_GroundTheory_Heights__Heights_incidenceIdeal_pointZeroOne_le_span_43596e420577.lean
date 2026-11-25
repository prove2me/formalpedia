-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_incidenceIdeal_pointZeroOne_le_span_43596e420577
-- name    : P2M_GroundTheory_Heights__Heights_incidenceIdeal_pointZeroOne_le_span_43596e420577
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:19.364732+00:00
-- url     : https://prove2.me/theorems/31b7a89b-68dd-5a21-aaea-96fe1a262ed5
-- title:
--   P2 M Ground Theory Heights  Heights incidence Ideal point Zero One le span 43596e420577: P2 M Ground Theory Heights  Heights incidence Ideal point Zero One le span 43596e420577
-- statement:
--   The P2 M Ground Theory Heights  Heights incidence Ideal point Zero One le span 43596e420577 construction uses the P2 M Ground Theory Heights  Heights incidence Ideal point Zero One le span 43596e420577 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartMax.lean#L75-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartMax.lean#L75-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
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

theorem P2M_GroundTheory_Heights__Heights_incidenceIdeal_pointZeroOne_le_span_43596e420577 :
    incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ≤ Ideal.span {qLine} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«incidenceIdeal_pointZeroOne_le_span» := P2M_GroundTheory_Heights__Heights_incidenceIdeal_pointZeroOne_le_span_43596e420577
