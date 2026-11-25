-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_smulSub
-- name    : PI.Dv.TIW.idx_smulSub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:28:51.134501+00:00
-- url     : https://prove2.me/theorems/e5f3a138-b7e3-46e9-9142-dced3d8018f9
-- title:
--   TIW: idx smul Sub
-- statement:
--   The TIW construction uses the idx smul Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L139-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L139-L162

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

theorem PI.Dv.TIW.idx_smulSub (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub d M) = (Formalism.HN.rkK M : ℤ) * vAdd w d := by sorry
