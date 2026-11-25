-- Prove2me | Theorems.Thm_PI_Tr_numeric_main
-- name    : PI.Tr.numeric_main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:29.258724+00:00
-- url     : https://prove2.me/theorems/2795638b-b543-4646-b9db-591de50b91d2
-- title:
--   Tr: numeric main
-- statement:
--   The Tr construction uses the numeric main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/NumericMain.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/NumericMain.lean#L10-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_GaussAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_NumericMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped Real
open PI PI.Tr

theorem PI.Tr.numeric_main : 9 / 4 * Real.exp (-(2 * π / 5)) + 2 * (4 * Real.exp (-(25 * π / 24))) < 1 := by sorry
