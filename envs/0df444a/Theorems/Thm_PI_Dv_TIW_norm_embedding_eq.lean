-- Prove2me | Theorems.Thm_PI_Dv_TIW_norm_embedding_eq
-- name    : PI.Dv.TIW.norm_embedding_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:05.785808+00:00
-- url     : https://prove2.me/theorems/c588b915-2bae-4044-89f8-e8353c62b468
-- title:
--   TIW: norm embedding eq
-- statement:
--   The TIW construction uses the norm embedding eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L47-L56

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

theorem PI.Dv.TIW.norm_embedding_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(vAdd v x)) := by sorry
