-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kUnitWtLin_shift
-- name    : ReciprocityTheory.ChartRestriction.DS.kUnitWtLin_shift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:52:33.953217+00:00
-- url     : https://prove2.me/theorems/b20e9af8-8b6c-5a94-8320-f21e938c8fa6
-- title:
--   DS: k Unit Wt Lin shift
-- statement:
--   The DS construction uses the k Unit Wt Lin shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean#L71-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.kUnitWtLin_shift (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by sorry
