-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_psum_zero
-- name    : PI.UnitaryGroupMassFormula.JCC.Ck.psum_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:48.820172+00:00
-- url     : https://prove2.me/theorems/683ae1e0-96e7-5ea0-a29a-481a0a461682
-- title:
--   Ck: psum zero
-- statement:
--   The Ck construction uses the psum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PCkPartials.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PCkPartials.lean#L15-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PCkPartials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC PI.UnitaryGroupMassFormula.JCC.Ck
variable {d : ℕ}

theorem PI.UnitaryGroupMassFormula.JCC.Ck.psum_zero (y h : Fin d → ℝ) : psum y h 0 = y := by sorry
