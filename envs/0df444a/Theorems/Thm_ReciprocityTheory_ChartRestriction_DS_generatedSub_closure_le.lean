-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_generatedSub_closure_le
-- name    : ReciprocityTheory.ChartRestriction.DS.generatedSub_closure_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:21.877909+00:00
-- url     : https://prove2.me/theorems/48e0f1ed-3399-559e-ac40-b42b172fef72
-- title:
--   DS: generated Sub closure le
-- statement:
--   The DS construction uses the generated Sub closure le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L92-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L92-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.generatedSub_closure_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (A : Submodule ℂ H) (hA : IsClosed (A : Set H))
    (hVA : ∀ g ∈ UJset ε, ∀ v ∈ V, σ g (v : H) ∈ A) :
    ((genSub E V).map D.subtype).topologicalClosure ≤ A := by sorry
