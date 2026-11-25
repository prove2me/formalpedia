-- Prove2me | Theorems.Thm_PI_Mk_schurPoly_eval_zero
-- name    : PI.Mk.schurPoly_eval_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:47.904801+00:00
-- url     : https://prove2.me/theorems/4fe491ac-4fc7-4102-9195-d66c65df4237
-- title:
--   Mk: schur Poly eval zero
-- statement:
--   The Mk construction uses the schur Poly eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/MinkowskiBoundOfSteps.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/MinkowskiBoundOfSteps.lean#L23-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_MinkowskiBoundOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset Polynomial

theorem PI.Mk.schurPoly_eval_zero (N ℓ m y : ℕ) (h1 : y ≠ 0) (h2 : y ≤ m) :
    (schurPoly N ℓ m).eval ((N : ℤ) - (ℓ : ℤ) * (y : ℤ)) = 0 := by sorry
