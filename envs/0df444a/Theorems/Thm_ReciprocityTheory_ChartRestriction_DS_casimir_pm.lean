-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_pm
-- name    : ReciprocityTheory.ChartRestriction.DS.casimir_pm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:32.452883+00:00
-- url     : https://prove2.me/theorems/a99fa6a4-9fdf-53fc-aaa8-5fa424d51a92
-- title:
--   DS: casimir pm
-- statement:
--   The DS construction uses the casimir pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L88-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L88-L122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.casimir_pm {E : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (ε : Fin n → Bool) :
    casimir E = casimirK ε E + (2 : ℂ) • ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i -
      (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • E a a := by sorry
