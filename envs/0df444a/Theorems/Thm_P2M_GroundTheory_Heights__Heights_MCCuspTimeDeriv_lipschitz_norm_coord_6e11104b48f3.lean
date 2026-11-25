-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_lipschitz_norm_coord_6e11104b48f3
-- name    : P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_lipschitz_norm_coord_6e11104b48f3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:43.967031+00:00
-- url     : https://prove2.me/theorems/4db41e7e-3688-4466-9613-5e6c1711ce7a
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp Time Deriv lipschitz norm coord 6e11104b48f3: P2 M Ground Theory Heights  Heights MCCusp Time Deriv lipschitz norm coord 6e11104b48f3
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp Time Deriv lipschitz norm coord 6e11104b48f3 construction uses the P2 M Ground Theory Heights  Heights MCCusp Time Deriv lipschitz norm coord 6e11104b48f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspTimeDeriv.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspTimeDeriv.lean#L10-L14

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

theorem P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_lipschitz_norm_coord_6e11104b48f3 {n : ℕ} (c : Fin n) :
    LipschitzWith 1 (fun w : Fin n → ℂ => ‖w c‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCuspTimeDeriv».«lipschitz_norm_coord» := P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_lipschitz_norm_coord_6e11104b48f3
