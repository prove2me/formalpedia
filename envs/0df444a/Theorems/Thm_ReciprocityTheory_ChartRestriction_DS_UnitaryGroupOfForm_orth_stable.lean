-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_orth_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.orth_stable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:25.731279+00:00
-- url     : https://prove2.me/theorems/500b7bf9-e44a-413c-9b08-78be240075a4
-- title:
--   Unitary Group Of Form: orth stable
-- statement:
--   The Unitary Group Of Form construction uses the orth stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L127-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L127-L139

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

theorem ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.orth_stable (hσ : IsURepOn (UJset ε) σ) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hg' : g' ∈ UJset ε) (hgg : g * g' = 1) (T : Submodule ℂ H) (hT : ∀ x ∈ T, σ g' x ∈ T) :
    ∀ x ∈ Tᗮ, σ g x ∈ Tᗮ := by sorry
