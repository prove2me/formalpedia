-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_le_natSub
-- name    : PI.Dv.TIW.idx_le_natSub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:28:26.271964+00:00
-- url     : https://prove2.me/theorems/8091a75d-c780-4dc1-bd10-c7fd6f5b996c
-- title:
--   TIW: idx le nat Sub
-- statement:
--   The TIW construction uses the idx le nat Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L98-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L98-L109

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

theorem PI.Dv.TIW.idx_le_natSub (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 0 < m)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub ((m : ℕ) : K) M) ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((m : ℕ) : K) := by sorry
