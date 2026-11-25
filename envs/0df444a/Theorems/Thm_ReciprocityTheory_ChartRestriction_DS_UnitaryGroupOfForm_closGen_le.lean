-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_closGen_le
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.closGen_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:08.191398+00:00
-- url     : https://prove2.me/theorems/c756cd2d-cece-4599-8649-98d3d8ce22de
-- title:
--   Unitary Group Of Form: clos Gen le
-- statement:
--   The Unitary Group Of Form construction uses the clos Gen le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L186-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L186-L193

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
variable {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.closGen_le (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) (V : Submodule ℂ D) (hV : ∀ v ∈ V, (v : H) ∈ T) :
    ((genSub E V).map D.subtype).topologicalClosure ≤ T := by sorry
