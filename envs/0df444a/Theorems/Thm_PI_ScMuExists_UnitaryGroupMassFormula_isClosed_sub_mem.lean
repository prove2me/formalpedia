-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_sub_mem
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.isClosed_sub_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:37:59.894343+00:00
-- url     : https://prove2.me/theorems/fb753ccb-774f-41bd-a0df-25253d6eb497
-- title:
--   Unitary Group Mass Formula: is Closed sub mem
-- statement:
--   The Unitary Group Mass Formula construction uses the is Closed sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L102-L106

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}

theorem PI.ScMuExists.UnitaryGroupMassFormula.isClosed_sub_mem (x : Fin n → ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ W} := by sorry
