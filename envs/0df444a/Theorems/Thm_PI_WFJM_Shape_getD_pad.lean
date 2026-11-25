-- Prove2me | Theorems.Thm_PI_WFJM_Shape_getD_pad
-- name    : PI.WFJM.Shape.getD_pad
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:04.940383+00:00
-- url     : https://prove2.me/theorems/110d8a58-302c-47d8-8c90-0551c977b6b5
-- title:
--   Shape: get D pad
-- statement:
--   The Shape construction uses the get D pad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L114-L129

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

theorem PI.WFJM.Shape.getD_pad (x y : List ℤ) (k i : ℕ) : (pad x k y).getD i 0 =
    if h : i < x.length then ((x[i] : ℤ) : ℚ) else if i < x.length + k then 0
      else ((y.getD (i - x.length - k) 0 : ℤ) : ℚ) := by sorry
