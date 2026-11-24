-- Prove2me | Theorems.Thm_PI_WFJM_Shape_natFloor_of_int
-- name    : PI.WFJM.Shape.natFloor_of_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:22.76285+00:00
-- url     : https://prove2.me/theorems/3cdca956-ebf1-41d8-85d4-ffa563b34440
-- title:
--   Shape: nat Floor of int
-- statement:
--   The Shape construction uses the nat Floor of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L105-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L105-L112

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

theorem PI.WFJM.Shape.natFloor_of_int (x : ℚ) (z : ℤ) (hz : (z : ℚ) = x) (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by sorry
