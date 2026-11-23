-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_skip_one_eq_succAbove
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.skip_one_eq_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:55.672653+00:00
-- url     : https://prove2.me/theorems/838576bc-3fc3-4cab-b000-975d8dd56648
-- title:
--   Qm Border Full: skip one eq succ Above
-- statement:
--   The Qm Border Full construction uses the skip one eq succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L23-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.skip_one_eq_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) : skip1 p i = p.succAbove i := by sorry
