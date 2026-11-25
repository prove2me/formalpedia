-- Prove2me | Theorems.Thm_PI_Dv_TIW_abs_norm_le
-- name    : PI.Dv.TIW.abs_norm_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:19.728288+00:00
-- url     : https://prove2.me/theorems/7cbf22b0-ea06-493f-93bb-01fad3a2283e
-- title:
--   TIW: abs norm le
-- statement:
--   The TIW construction uses the abs norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L121-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L121-L134

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero

theorem PI.Dv.TIW.abs_norm_le {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ) (hB : 0 ≤ B)
    (hσ : ∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) :
    |((Algebra.norm ℤ x : ℤ) : ℝ)| ≤ B ^ Module.finrank ℚ K := by sorry
