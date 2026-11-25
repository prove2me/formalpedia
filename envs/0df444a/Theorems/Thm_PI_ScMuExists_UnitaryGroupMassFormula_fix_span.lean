-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_fix_span
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.fix_span
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:41:13.062894+00:00
-- url     : https://prove2.me/theorems/61b3ea91-aa10-521d-9b1d-ed4d9b0938ed
-- title:
--   Unitary Group Mass Formula: fix span
-- statement:
--   The Unitary Group Mass Formula construction uses the fix span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L126-L134

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

theorem PI.ScMuExists.UnitaryGroupMassFormula.fix_span {W : Set (Fin n → ℂ)} {g : Matrix (Fin n) (Fin n) ℂ} (hW : ∀ x ∈ W, g *ᵥ x = x) :
    ∀ x ∈ Submodule.span ℂ W, g *ᵥ x = x := by sorry
