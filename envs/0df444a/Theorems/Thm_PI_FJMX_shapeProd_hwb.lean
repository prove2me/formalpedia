-- Prove2me | Theorems.Thm_PI_FJMX_shapeProd_hwb
-- name    : PI.FJMX.shapeProd_hwb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:29.983177+00:00
-- url     : https://prove2.me/theorems/683c8f8e-4adc-463c-adbc-3ae10598bbe7
-- title:
--   FJMX: shape Prod hwb
-- statement:
--   The FJMX construction uses the shape Prod hwb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L128-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L128-L156

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m n : ℕ}

theorem PI.FJMX.shapeProd_hwb (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (α : List ℕ) :
    PI.FJMB.HWB ι (PI.FJM.shapeProd (blkM ι) α) := by sorry
