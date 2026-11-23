-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_norm_actM_pow_le_of_inK
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_norm_actM_pow_le_of_inK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:30.634595+00:00
-- url     : https://prove2.me/theorems/cc8c6383-11f3-4d45-b815-e0f1c95aa454
-- title:
--   DS: exists norm act M pow le of in K
-- statement:
--   The DS construction uses the exists norm act M pow le of in K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ClosureK.lean#L47-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ClosureK.lean#L47-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.exists_norm_actM_pow_le_of_inK {V : Submodule ℂ D} (hE : IsGlRep E)
    (hV : IsKStableSub ε E V) (hVf : FiniteDimensional ℂ V) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : inK ε Z) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ layer ε E V k, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by sorry
