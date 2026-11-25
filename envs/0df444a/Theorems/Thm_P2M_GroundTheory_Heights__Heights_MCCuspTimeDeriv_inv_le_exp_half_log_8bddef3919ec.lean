-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_inv_le_exp_half_log_8bddef3919ec
-- name    : P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_inv_le_exp_half_log_8bddef3919ec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:17.588912+00:00
-- url     : https://prove2.me/theorems/09f26161-98b0-587e-b278-53e289c3d029
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp Time Deriv inv le exp half log 8bddef3919ec: P2 M Ground Theory Heights  Heights MCCusp Time Deriv inv le exp half log 8bddef3919ec
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp Time Deriv inv le exp half log 8bddef3919ec construction uses the P2 M Ground Theory Heights  Heights MCCusp Time Deriv inv le exp half log 8bddef3919ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspTimeDeriv.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspTimeDeriv.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspTimeDeriv
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
open GroundTheory.Heights₂.Heights.MCCuspTimeDeriv

theorem P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_inv_le_exp_half_log_8bddef3919ec {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ Real.exp (Real.log (x ^ 2)⁻¹ / 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCuspTimeDeriv».«inv_le_exp_half_log» := P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_inv_le_exp_half_log_8bddef3919ec
