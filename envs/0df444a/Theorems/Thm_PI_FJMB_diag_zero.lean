-- Prove2me | Theorems.Thm_PI_FJMB_diag_zero
-- name    : PI.FJMB.diag_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:46.35186+00:00
-- url     : https://prove2.me/theorems/bc27289e-706a-4f41-abe9-b8783abcbec5
-- title:
--   FJMB: diag zero
-- statement:
--   The FJMB construction uses the diag zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurDiag.lean#L131-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurDiag.lean#L131-L166

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.diag_zero : ∀ (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι → ∀ f : MvPolynomial σ ℂ,
    HWB ι f → aeval (killS (offD ι)) f = 0 → f = 0 := by sorry
