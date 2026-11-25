-- Prove2me | Theorems.Thm_PI_Dv_TIW_log_norm_embedding
-- name    : PI.Dv.TIW.log_norm_embedding
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:53.301952+00:00
-- url     : https://prove2.me/theorems/c8b90902-2f39-4ff5-82c0-2e43884eea7f
-- title:
--   TIW: log norm embedding
-- statement:
--   The TIW construction uses the log norm embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L58-L62

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

theorem PI.Dv.TIW.log_norm_embedding {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((vAdd v x : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) := by sorry
