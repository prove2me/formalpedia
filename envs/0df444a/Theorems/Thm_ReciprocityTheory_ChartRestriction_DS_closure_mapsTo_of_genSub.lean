-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_closure_mapsTo_of_genSub
-- name    : ReciprocityTheory.ChartRestriction.DS.closure_mapsTo_of_genSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:52.57443+00:00
-- url     : https://prove2.me/theorems/978547d4-5805-4fd3-b56a-b2832a77f16a
-- title:
--   DS: closure maps To of gen Sub
-- statement:
--   The DS construction uses the closure maps To of gen Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Closure.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Closure.lean#L38-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Analytic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
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

theorem ReciprocityTheory.ChartRestriction.DS.closure_mapsTo_of_genSub {V : Submodule ℂ D} (T : H →L[ℂ] H)
    (hT : ∀ v : D, v ∈ genSub E V → T (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure)
    {x : H} (hx : x ∈ ((genSub E V).map D.subtype).topologicalClosure) :
    T x ∈ ((genSub E V).map D.subtype).topologicalClosure := by sorry
