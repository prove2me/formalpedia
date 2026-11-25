-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_isInt_star
-- name    : PI.UnitaryGroupMassFormula.CntFormula.isInt_star
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:23.83991+00:00
-- url     : https://prove2.me/theorems/97d28db5-db96-428d-88c9-1b6a4a3df1ea
-- title:
--   Cnt Formula: is Int star
-- statement:
--   The Cnt Formula construction uses the is Int star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/IsIntIntCast.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/IsIntIntCast.lean#L18-L19

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

theorem PI.UnitaryGroupMassFormula.CntFormula.isInt_star [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) := by sorry
