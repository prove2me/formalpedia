-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bcas_sum_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.bcas_sum_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:38.601854+00:00
-- url     : https://prove2.me/theorems/121412d9-afde-406c-b216-7bffea0ba4ab
-- title:
--   DS: bcas sum apply
-- statement:
--   The DS construction uses the bcas sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCas.lean#L17-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.bcas_sum_apply {k : ℕ} {ι : Type*} (s : Finset ι) (G : ι → Big n k M)
    (κ : Fin k → Fin n × Fin n) : (∑ i ∈ s, G i) κ = ∑ i ∈ s, G i κ := by sorry
