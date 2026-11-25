-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_zero_one_dvd_sub_substZeroOne_0e2e6d7fe4f3
-- name    : P2M_GroundTheory_Heights__Heights_X_zero_one_dvd_sub_substZeroOne_0e2e6d7fe4f3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:34.178486+00:00
-- url     : https://prove2.me/theorems/dece986a-dcf5-48dc-a096-ba3f9791c3f7
-- title:
--   P2 M Ground Theory Heights  Heights X zero one dvd sub subst Zero One 0e2e6d7fe4f3: P2 M Ground Theory Heights  Heights X zero one dvd sub subst Zero One 0e2e6d7fe4f3
-- statement:
--   The P2 M Ground Theory Heights  Heights X zero one dvd sub subst Zero One 0e2e6d7fe4f3 construction uses the P2 M Ground Theory Heights  Heights X zero one dvd sub subst Zero One 0e2e6d7fe4f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartMax.lean#L58-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartMax.lean#L58-L73

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

theorem P2M_GroundTheory_Heights__Heights_X_zero_one_dvd_sub_substZeroOne_0e2e6d7fe4f3 (g : MvPolynomial (Fin 1 × Fin 2) ℚ) : X (0, 1) ∣ g - substZeroOne g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«X_zero_one_dvd_sub_substZeroOne» := P2M_GroundTheory_Heights__Heights_X_zero_one_dvd_sub_substZeroOne_0e2e6d7fe4f3
