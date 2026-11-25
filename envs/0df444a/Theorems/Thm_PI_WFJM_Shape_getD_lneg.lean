-- Prove2me | Theorems.Thm_PI_WFJM_Shape_getD_lneg
-- name    : PI.WFJM.Shape.getD_lneg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:05.485627+00:00
-- url     : https://prove2.me/theorems/8c500e5f-9fe5-4286-a16e-317ce10ea7f4
-- title:
--   Shape: get D lneg
-- statement:
--   The Shape construction uses the get D lneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L131-L135

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}

theorem PI.WFJM.Shape.getD_lneg {m : ℕ} (α : Fin m → ℕ) (t : ℕ) (ht : t < m) :
    (lneg α).getD t 0 = -(α ⟨m - 1 - t, by omega⟩ : ℤ) := by sorry
