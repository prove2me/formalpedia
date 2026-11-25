-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_khw_decomp
-- name    : ReciprocityTheory.ChartRestriction.DS.layer_khw_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:54.345134+00:00
-- url     : https://prove2.me/theorems/fa777196-e7dd-4c2b-87d8-5658738ff1bc
-- title:
--   DS: layer khw decomp
-- statement:
--   The DS construction uses the layer khw decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerOrth.lean#L37-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerOrth.lean#L37-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.layer_khw_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V k) {μ : Fin n → ℝ}
    (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ ws : Fin k → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin k, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧
        (∀ u ∈ layer ε E V (j : ℕ), inner ℂ u (ws j) = 0) ∧ IsKHWVec ε E μ (ws j) := by sorry
