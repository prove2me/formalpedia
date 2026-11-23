-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_layer_of_mem_genSub
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_layer_of_mem_genSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:11.311861+00:00
-- url     : https://prove2.me/theorems/fd048105-48e2-4064-b7fd-55e3c33413af
-- title:
--   DS: exists layer of mem gen Sub
-- statement:
--   The DS construction uses the exists layer of mem gen Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L16-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
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
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.exists_layer_of_mem_genSub (hE : IsGlRep E) (hVk : IsKStableSub ε E V) {w : M}
    (hw : w ∈ genSub E V) : ∃ m, w ∈ layer ε E V m := by sorry
