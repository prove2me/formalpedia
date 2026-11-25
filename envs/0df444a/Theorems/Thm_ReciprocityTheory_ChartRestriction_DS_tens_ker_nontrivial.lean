-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tens_ker_nontrivial
-- name    : ReciprocityTheory.ChartRestriction.DS.tens_ker_nontrivial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:33.21444+00:00
-- url     : https://prove2.me/theorems/1339707b-e718-54f8-aa53-e8dbe69ac4f0
-- title:
--   DS: tens ker nontrivial
-- statement:
--   The DS construction uses the tens ker nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L235-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L235-L246

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.tens_ker_nontrivial (T : Module.End ℂ M) {V : Submodule ℂ M} {x : TensorProduct ℂ M (Fock n)}
    (hx : x ∈ LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (hx0 : x ≠ 0) (hTx : TensorProduct.map T LinearMap.id x = 0) : ∃ v ∈ V, v ≠ 0 ∧ T v = 0 := by sorry
