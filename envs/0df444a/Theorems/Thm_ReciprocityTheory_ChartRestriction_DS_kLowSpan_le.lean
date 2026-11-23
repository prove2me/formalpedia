-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_le
-- name    : ReciprocityTheory.ChartRestriction.DS.kLowSpan_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:50.005543+00:00
-- url     : https://prove2.me/theorems/95e69a0c-f2b4-438c-a5a7-54fc984c0605
-- title:
--   DS: k Low Span le
-- statement:
--   The DS construction uses the k Low Span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L131-L144

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.kLowSpan_le {y : M} {T : Submodule ℂ M} (hT : IsKStableSub ε E T) (hy : y ∈ T) :
    kLowSpan ε E y ≤ T := by sorry
