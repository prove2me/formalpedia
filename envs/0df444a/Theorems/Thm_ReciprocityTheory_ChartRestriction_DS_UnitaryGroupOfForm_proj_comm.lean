-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_proj_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.proj_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:33.083282+00:00
-- url     : https://prove2.me/theorems/24288e29-c446-49b9-966a-be9ae5bc7725
-- title:
--   Unitary Group Of Form: proj comm
-- statement:
--   The Unitary Group Of Form construction uses the proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L141-L148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
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
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.proj_comm (T : Submodule ℂ H) [T.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (h1 : ∀ x ∈ T, A x ∈ T) (h2 : ∀ x ∈ Tᗮ, A x ∈ Tᗮ) (x : H) :
    T.starProjection (A x) = A (T.starProjection x) := by sorry
