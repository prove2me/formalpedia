-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKHWVec_starProjection
-- name    : ReciprocityTheory.ChartRestriction.DS.isKHWVec_starProjection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:57.698412+00:00
-- url     : https://prove2.me/theorems/c8c4cc9d-7c3f-4228-aece-70c2cf40ee44
-- title:
--   DS: is KHWVec star Projection
-- statement:
--   The DS construction uses the is KHWVec star Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerOrth.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/LayerOrth.lean#L17-L29

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

theorem ReciprocityTheory.ChartRestriction.DS.isKHWVec_starProjection (hU : IsKUnitary ε E) {S : Submodule ℂ M}
    [S.HasOrthogonalProjection] (hS : IsKStableSub ε E S) {μ : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (S.starProjection w) := by sorry
