-- Prove2me | Theorems.Thm_PI_WFJM_Shape_length_lpos
-- name    : PI.WFJM.Shape.length_lpos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:42.796836+00:00
-- url     : https://prove2.me/theorems/7f98dbb8-8fca-4f86-9a81-dc05d3f73735
-- title:
--   Shape: length lpos
-- statement:
--   The Shape construction uses the length lpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L23-L23

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

theorem PI.WFJM.Shape.length_lpos {m : ℕ} (α : Fin m → ℕ) : (lpos α).length = m := by sorry
