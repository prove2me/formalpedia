-- Prove2me | Theorems.Thm_PI_WFJM_Shape_neg_iff
-- name    : PI.WFJM.Shape.neg_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:18.475833+00:00
-- url     : https://prove2.me/theorems/a5bc0be1-eb64-46f8-9aea-815dab68b015
-- title:
--   Shape: neg iff
-- statement:
--   The Shape construction uses the neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L58-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L58-L88

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

theorem PI.WFJM.Shape.neg_iff (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin n) :
    f i < 0 ↔ n - nN f ≤ (i : ℕ) := by sorry
