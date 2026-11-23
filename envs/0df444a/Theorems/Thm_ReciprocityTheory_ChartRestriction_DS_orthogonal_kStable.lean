-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_orthogonal_kStable
-- name    : ReciprocityTheory.ChartRestriction.DS.orthogonal_kStable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:21.771806+00:00
-- url     : https://prove2.me/theorems/d25daee5-6852-4dd4-a853-36bce6e41969
-- title:
--   DS: orthogonal k Stable
-- statement:
--   The DS construction uses the orthogonal k Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean#L112-L118

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

theorem ReciprocityTheory.ChartRestriction.DS.orthogonal_kStable (hU : IsKUnitary ε A) {S : Submodule ℂ X} (hS : IsKStableSub ε A S) :
    IsKStableSub ε A Sᗮ := by sorry
