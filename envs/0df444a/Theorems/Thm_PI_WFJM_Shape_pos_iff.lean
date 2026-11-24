-- Prove2me | Theorems.Thm_PI_WFJM_Shape_pos_iff
-- name    : PI.WFJM.Shape.pos_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:27.154795+00:00
-- url     : https://prove2.me/theorems/f487946a-9bc8-4e0c-87ca-df8fe381c135
-- title:
--   Shape: pos iff
-- statement:
--   The Shape construction uses the pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L27-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L27-L56

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

theorem PI.WFJM.Shape.pos_iff (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin n) :
    0 < f i ↔ (i : ℕ) < nP f := by sorry
