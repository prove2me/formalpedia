-- Prove2me | Theorems.Thm_PI_Dv_TIW_vAdd_prod
-- name    : PI.Dv.TIW.vAdd_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:13.856257+00:00
-- url     : https://prove2.me/theorems/306d02b0-8ed1-4cdf-9e96-399fdd1470c4
-- title:
--   TIW: v Add prod
-- statement:
--   The TIW construction uses the v Add prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L23-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
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
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K]

theorem PI.Dv.TIW.vAdd_prod (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by sorry
