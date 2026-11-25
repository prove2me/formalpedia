-- Prove2me | Theorems.Thm_PI_WFJM_Shape_lneg_eq_of_sq
-- name    : PI.WFJM.Shape.lneg_eq_of_sq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:58.128901+00:00
-- url     : https://prove2.me/theorems/cd6f1fca-25bd-4396-a7f3-92a95daa9133
-- title:
--   Shape: lneg eq of sq
-- statement:
--   The Shape construction uses the lneg eq of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L192-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L192-L199

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

theorem PI.WFJM.Shape.lneg_eq_of_sq {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lneg α = lneg β := by sorry
