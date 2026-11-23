-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_big_weight
-- name    : ReciprocityTheory.ChartRestriction.DS.khw_big_weight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:04.810734+00:00
-- url     : https://prove2.me/theorems/a38527e7-a21e-4a29-b1f9-01c0ef114ae7
-- title:
--   DS: khw big weight
-- statement:
--   The DS construction uses the khw big weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Weights.lean#L66-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Weights.lean#L66-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.khw_big_weight (hE : IsGlRep E) (hV : IsKIrrHW ε E Λ V) {k : ℕ} {F : Big n k M}
    (hF : F ∈ ncV ε V k) (hF0 : F ≠ 0) {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E k) ν F) :
    IsNCSum ε k (ν - Λ) := by sorry
