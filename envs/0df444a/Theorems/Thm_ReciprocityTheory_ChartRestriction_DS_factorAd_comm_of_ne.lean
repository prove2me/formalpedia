-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_comm_of_ne
-- name    : ReciprocityTheory.ChartRestriction.DS.factorAd_comm_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:21.634844+00:00
-- url     : https://prove2.me/theorems/49f6629a-75bf-4683-addf-dfc9e045cd97
-- title:
--   DS: factor Ad comm of ne
-- statement:
--   The DS construction uses the factor Ad comm of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L67-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
variable {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.factorAd_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by sorry
