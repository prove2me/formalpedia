-- Prove2me | Theorems.Thm_PI_Dv_TIW_finsum_eq_log_norm
-- name    : PI.Dv.TIW.finsum_eq_log_norm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:31:28.469857+00:00
-- url     : https://prove2.me/theorems/24cad80d-a992-5623-8daf-2e5d2433d7f7
-- title:
--   TIW: finsum eq log norm
-- statement:
--   The TIW construction uses the finsum eq log norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L64-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L64-L119

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

theorem PI.Dv.TIW.finsum_eq_log_norm {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (hx : x ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      Real.log |((Algebra.norm ℤ x : ℤ) : ℝ)| / (Module.finrank ℚ K : ℝ) := by sorry
