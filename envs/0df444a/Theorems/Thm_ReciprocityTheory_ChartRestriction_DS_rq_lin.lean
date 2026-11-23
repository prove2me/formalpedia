-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_lin
-- name    : ReciprocityTheory.ChartRestriction.DS.rq_lin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:40.613901+00:00
-- url     : https://prove2.me/theorems/71d03c67-5008-40f6-ac4e-c2e7e0378093
-- title:
--   DS: rq lin
-- statement:
--   The DS construction uses the rq lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L175-L189

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

theorem ReciprocityTheory.ChartRestriction.DS.rq_lin {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : D) (a b : ℂ)
    {S T : Matrix (Fin n) (Fin n) ℂ}
    (hS : σ k ((actM E S v : D) : H) =
      ((actM E (k * S * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H))
    (hT : σ k ((actM E T v : D) : H) =
      ((actM E (k * T * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H)) :
    σ k ((actM E (a • S + b • T) v : D) : H) =
      ((actM E (k * (a • S + b • T) * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by sorry
