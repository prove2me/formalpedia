-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inner_E
-- name    : ReciprocityTheory.ChartRestriction.DS.rorth_inner_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:36.989052+00:00
-- url     : https://prove2.me/theorems/343000fc-759f-40c9-87e7-1757f8a09a58
-- title:
--   DS: rorth inner E
-- statement:
--   The DS construction uses the rorth inner E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L187-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L187-L202

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.rorth_inner_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (φ : H →L[ℂ] H) (hφ : ∀ v : V, φ ((v : D) : H) = j v)
    {a b : Fin n} (h : ε a = ε b) (v : V) (x : D) :
    inner ℂ (φ ((E a b v : D) : H)) (x : H) = inner ℂ (j v) ((E b a x : D) : H) := by sorry
