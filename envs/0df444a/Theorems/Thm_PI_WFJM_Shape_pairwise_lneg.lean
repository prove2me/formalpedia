-- Prove2me | Theorems.Thm_PI_WFJM_Shape_pairwise_lneg
-- name    : PI.WFJM.Shape.pairwise_lneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:09.036071+00:00
-- url     : https://prove2.me/theorems/6cc2cb54-ef91-45ba-9583-6ca146a59f41
-- title:
--   Shape: pairwise lneg
-- statement:
--   The Shape construction uses the pairwise lneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L207-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L207-L213

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

theorem PI.WFJM.Shape.pairwise_lneg {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lneg α).Pairwise (· ≥ ·) := by sorry
