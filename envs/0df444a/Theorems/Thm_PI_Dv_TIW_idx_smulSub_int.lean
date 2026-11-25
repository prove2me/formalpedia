-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_smulSub_int
-- name    : PI.Dv.TIW.idx_smulSub_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:31.709212+00:00
-- url     : https://prove2.me/theorems/cb1dd65c-1016-427e-a92f-03dd25601982
-- title:
--   TIW: idx smul Sub int
-- statement:
--   The TIW construction uses the idx smul Sub int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L111-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L111-L137

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
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.idx_smulSub_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) = (Formalism.HN.rkK M : ℤ) * vAdd w (algebraMap (𝓞 K) K a) := by sorry
