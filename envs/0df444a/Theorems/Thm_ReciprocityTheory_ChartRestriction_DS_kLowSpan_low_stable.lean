-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_low_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.kLowSpan_low_stable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:05.571969+00:00
-- url     : https://prove2.me/theorems/cf6a86f0-8c2a-5a20-b5d7-9736410c8cb4
-- title:
--   DS: k Low Span low stable
-- statement:
--   The DS construction uses the k Low Span low stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L72-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L72-L78

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

theorem ReciprocityTheory.ChartRestriction.DS.kLowSpan_low_stable {y : M} {c d : Fin n} (hcd : IsKLow ε (c, d)) :
    ∀ x ∈ kLowSpan ε E y, E c d x ∈ kLowSpan ε E y := by sorry
