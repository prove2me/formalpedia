-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_isInt_intCast
-- name    : PI.UnitaryGroupMassFormula.CntFormula.isInt_intCast
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:27.179069+00:00
-- url     : https://prove2.me/theorems/6ffd663a-e215-4067-b717-55911a214724
-- title:
--   Cnt Formula: is Int int Cast
-- statement:
--   The Cnt Formula construction uses the is Int int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/IsIntIntCast.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/IsIntIntCast.lean#L15-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_IsIntIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open NumberField
variable {K : Type} [Field K] [NumberField K]

theorem PI.UnitaryGroupMassFormula.CntFormula.isInt_intCast (n : ℤ) : IsIntegral ℤ (n : K) := by sorry
