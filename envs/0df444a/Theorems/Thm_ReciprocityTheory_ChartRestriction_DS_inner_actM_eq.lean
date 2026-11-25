-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_actM_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.inner_actM_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:16.028672+00:00
-- url     : https://prove2.me/theorems/419bebc1-39d2-4db0-b9ee-db2f2adedd37
-- title:
--   DS: inner act M eq
-- statement:
--   The DS construction uses the inner act M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L86-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L86-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
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
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.inner_actM_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (M : Matrix (Fin n) (Fin n) ℂ) (x y : D) :
    inner ℂ (actM E M x) y = inner ℂ x (actM E (Jm ε * Mᴴ * Jm ε) y) := by sorry
