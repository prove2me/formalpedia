-- Prove2me | Theorems.Thm_PI_WFJM_Shape_pairwise_lpos
-- name    : PI.WFJM.Shape.pairwise_lpos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:14.913093+00:00
-- url     : https://prove2.me/theorems/4e97f25f-3d92-43cf-823d-4c52066f5ec2
-- title:
--   Shape: pairwise lpos
-- statement:
--   The Shape construction uses the pairwise lpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L201-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeFromFacts.lean#L201-L205

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

theorem PI.WFJM.Shape.pairwise_lpos {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lpos α).Pairwise (· ≥ ·) := by sorry
