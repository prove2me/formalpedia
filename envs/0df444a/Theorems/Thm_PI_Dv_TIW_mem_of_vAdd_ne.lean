-- Prove2me | Theorems.Thm_PI_Dv_TIW_mem_of_vAdd_ne
-- name    : PI.Dv.TIW.mem_of_vAdd_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:07.016043+00:00
-- url     : https://prove2.me/theorems/d3e03053-2eb9-429c-93f3-31d80e416144
-- title:
--   TIW: mem of v Add ne
-- statement:
--   The TIW construction uses the mem of v Add ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/FinsumEqLogNorm.lean#L23-L30

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

theorem PI.Dv.TIW.mem_of_vAdd_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (h : vAdd w (algebraMap (𝓞 K) K x) ≠ 0) : x ∈ w.asIdeal := by sorry
