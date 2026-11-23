-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_main_G
-- name    : ReciprocityTheory.ChartRestriction.DS.rq_main_G
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:38.689945+00:00
-- url     : https://prove2.me/theorems/61dbafc4-b400-4f74-9a4d-f9edd8d7435d
-- title:
--   DS: rq main G
-- statement:
--   The DS construction uses the rq main G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L108-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L108-L138

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem ReciprocityTheory.ChartRestriction.DS.rq_main_G {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) :
    σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by sorry
