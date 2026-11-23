-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_cm_basis_of_not_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_cm_basis_of_not_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:59.590442+00:00
-- url     : https://prove2.me/theorems/976182ce-cfc4-4241-a43f-7ea7b58859d9
-- title:
--   DS: lf cm basis of not mem
-- statement:
--   The DS construction uses the lf cm basis of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L66-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
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

theorem ReciprocityTheory.ChartRestriction.DS.lf_cm_basis_of_not_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    cmFock x.1 x.2 (fockBasis n S) = 0 := by sorry
