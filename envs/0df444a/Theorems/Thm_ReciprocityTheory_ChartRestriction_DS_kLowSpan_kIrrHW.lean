-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_kIrrHW
-- name    : ReciprocityTheory.ChartRestriction.DS.kLowSpan_kIrrHW
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:42.84475+00:00
-- url     : https://prove2.me/theorems/fdbf9c35-0a93-4dec-a169-06abf91b46e6
-- title:
--   DS: k Low Span k Irr HW
-- statement:
--   The DS construction uses the k Low Span k Irr HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L244-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L244-L286

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
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
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.kLowSpan_kIrrHW (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E μ y) (hy0 : y ≠ 0) (hfin : FiniteDimensional ℂ (kLowSpan ε E y)) :
    IsKIrrHW ε E μ (kLowSpan ε E y) := by sorry
