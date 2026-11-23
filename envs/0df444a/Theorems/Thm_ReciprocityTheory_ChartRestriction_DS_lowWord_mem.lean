-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.lowWord_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:44.867558+00:00
-- url     : https://prove2.me/theorems/a798bf04-b78a-4281-8f30-920d773f1221
-- title:
--   DS: low Word mem
-- statement:
--   The DS construction uses the low Word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean#L29-L32

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

theorem ReciprocityTheory.ChartRestriction.DS.lowWord_mem {y : M} {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, IsKLow ε p) :
    lowWord E y l ∈ kLowSpan ε E y := by sorry
