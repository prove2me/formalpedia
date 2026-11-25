-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_zDeriv
-- name    : PI.UnitaryGroupMassFormula.UsCost.zDeriv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:06.242816+00:00
-- url     : https://prove2.me/theorems/70cc756f-a21a-5654-8cd7-d1dec59d94d6
-- title:
--   Us Cost: z Deriv
-- statement:
--   The Us Cost construction uses the z Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZDeriv.lean#L14-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZDeriv.lean#L14-L87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost.DA PI.UnitaryGroupMassFormula.UsCost.DB

theorem PI.UnitaryGroupMassFormula.UsCost.zDeriv : ZDeriv := by sorry
