-- Prove2me | Theorems.Thm_PI_WFJM_Shape_length_lneg
-- name    : PI.WFJM.Shape.length_lneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:15.80503+00:00
-- url     : https://prove2.me/theorems/8a6a39d5-4434-40d2-bb1d-fbee62656fcc
-- title:
--   Shape: length lneg
-- statement:
--   The Shape construction uses the length lneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L25-L25

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

theorem PI.WFJM.Shape.length_lneg {m : ℕ} (α : Fin m → ℕ) : (lneg α).length = m := by sorry
