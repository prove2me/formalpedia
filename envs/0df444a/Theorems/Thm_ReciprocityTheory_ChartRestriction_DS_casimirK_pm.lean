-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_pm
-- name    : ReciprocityTheory.ChartRestriction.DS.casimirK_pm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:00.759688+00:00
-- url     : https://prove2.me/theorems/215e624b-07bb-45cc-ba3d-9e48f48ae31d
-- title:
--   DS: casimir K pm
-- statement:
--   The DS construction uses the casimir K pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L41-L49

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

theorem ReciprocityTheory.ChartRestriction.DS.casimirK_pm {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    casimirK ε F = ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, F a b * F b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, F a b * F b a := by sorry
