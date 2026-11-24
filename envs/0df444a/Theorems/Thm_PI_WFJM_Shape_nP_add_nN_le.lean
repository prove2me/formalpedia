-- Prove2me | Theorems.Thm_PI_WFJM_Shape_nP_add_nN_le
-- name    : PI.WFJM.Shape.nP_add_nN_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:20.719525+00:00
-- url     : https://prove2.me/theorems/347bdad8-2044-48f3-95be-13e2addc0b62
-- title:
--   Shape: n P add n N le
-- statement:
--   The Shape construction uses the n P add n N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L90-L103

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

theorem PI.WFJM.Shape.nP_add_nN_le (f : Fin n → ℚ) : nP f + nN f ≤ n := by sorry
