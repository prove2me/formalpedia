-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_inK_apply_mem_closure
-- name    : ReciprocityTheory.ChartRestriction.DS.exp_inK_apply_mem_closure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:20.443459+00:00
-- url     : https://prove2.me/theorems/0307d8b2-5793-4290-98e7-5db735f1c807
-- title:
--   DS: exp in K apply mem closure
-- statement:
--   The DS construction uses the exp in K apply mem closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ClosureK.lean#L77-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ClosureK.lean#L77-L100

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

theorem ReciprocityTheory.ChartRestriction.DS.exp_inK_apply_mem_closure (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp Z) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by sorry
