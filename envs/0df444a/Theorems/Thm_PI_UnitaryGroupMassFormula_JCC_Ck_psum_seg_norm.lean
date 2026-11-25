-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_psum_seg_norm
-- name    : PI.UnitaryGroupMassFormula.JCC.Ck.psum_seg_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:37.163021+00:00
-- url     : https://prove2.me/theorems/f567547c-ce80-5710-abc5-0dce897d3e0a
-- title:
--   Ck: psum seg norm
-- statement:
--   The Ck construction uses the psum seg norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PCkPartials.lean#L36-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PCkPartials.lean#L36-L53

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

theorem PI.UnitaryGroupMassFormula.JCC.Ck.psum_seg_norm (y h : Fin d → ℝ) (i : Fin d) {s : ℝ} (hs : |s| ≤ |h i|) :
    ‖psum y h i.val + s • Pi.single i (1 : ℝ) - y‖ ≤ ‖h‖ := by sorry
