-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_actM_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.actM_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:38.973318+00:00
-- url     : https://prove2.me/theorems/b394f22d-1a04-4393-83e4-ad93ec5e0a15
-- title:
--   Unitary Group Of Form: act M mem
-- statement:
--   The Unitary Group Of Form construction uses the act M mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L152-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IrredA.lean#L152-L172

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

theorem ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.actM_mem (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) (hv : (v : H) ∈ T) : ((actM E X v : D) : H) ∈ T := by sorry
