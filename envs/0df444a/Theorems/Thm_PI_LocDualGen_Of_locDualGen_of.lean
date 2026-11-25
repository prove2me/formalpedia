-- Prove2me | Theorems.Thm_PI_LocDualGen_Of_locDualGen_of
-- name    : PI.LocDualGen.Of.locDualGen_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:42.716595+00:00
-- url     : https://prove2.me/theorems/6cbb84f6-ad94-5413-b28f-7cf08fb38086
-- title:
--   Of: loc Dual Gen of
-- statement:
--   The Of construction uses the loc Dual Gen of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/LocDualGenOf.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/LocDualGenOf.lean#L10-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_AddCharKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_LocDualGenOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LocDualGen PI.LocDualGen.Of

theorem PI.LocDualGen.Of.locDualGen_of (h : PI.LocDualGen.W.FpDualUnram) : PI.LocDualGen.Stmt := by sorry
