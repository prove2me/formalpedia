-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_pow_mem_layer_of_inK
-- name    : ReciprocityTheory.ChartRestriction.DS.actM_pow_mem_layer_of_inK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:32.924309+00:00
-- url     : https://prove2.me/theorems/1dd1bd4f-d9d9-4d99-ae59-a640ad4ee356
-- title:
--   DS: act M pow mem layer of in K
-- statement:
--   The DS construction uses the act M pow mem layer of in K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ClosureK.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ClosureK.lean#L38-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.actM_pow_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ layer ε E V k := by sorry
