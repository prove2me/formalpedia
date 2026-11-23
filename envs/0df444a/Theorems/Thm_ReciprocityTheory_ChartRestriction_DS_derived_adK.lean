-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_derived_adK
-- name    : ReciprocityTheory.ChartRestriction.DS.derived_adK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:13.172878+00:00
-- url     : https://prove2.me/theorems/38852513-da28-4f8c-b753-e746e93222c5
-- title:
--   DS: derived ad K
-- statement:
--   The DS construction uses the derived ad K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L193-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L193-L202

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
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

theorem ReciprocityTheory.ChartRestriction.DS.derived_adK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by sorry
