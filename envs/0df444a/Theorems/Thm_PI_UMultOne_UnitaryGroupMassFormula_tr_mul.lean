-- Prove2me | Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_mul
-- name    : PI.UMultOne.UnitaryGroupMassFormula.tr_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:03.114232+00:00
-- url     : https://prove2.me/theorems/223a9f05-ba9c-5a7d-8869-d904aa55c959
-- title:
--   Unitary Group Mass Formula: tr mul
-- statement:
--   The Unitary Group Mass Formula construction uses the tr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean#L38-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set

theorem PI.UMultOne.UnitaryGroupMassFormula.tr_mul (m : ℕ) (x y : Matrix.unitaryGroup (Fin m) ℂ) : tr m (x * y) = tr m y * tr m x := by sorry
