-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_closure_genSub_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.closure_genSub_stable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:37.207204+00:00
-- url     : https://prove2.me/theorems/f579d68c-cd0a-4841-84e2-477f25657dfc
-- title:
--   DS: closure gen Sub stable
-- statement:
--   The DS construction uses the closure gen Sub stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Closure.lean#L98-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Closure.lean#L98-L133

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

theorem ReciprocityTheory.ChartRestriction.DS.closure_genSub_stable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∀ g ∈ UJset ε, ∀ x ∈ ((genSub E V).map D.subtype).topologicalClosure,
      σ g x ∈ ((genSub E V).map D.subtype).topologicalClosure := by sorry
