-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfa_cp_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.lfa_cp_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:24.736809+00:00
-- url     : https://prove2.me/theorems/1830b868-23c5-45b8-afcc-cb8704880db0
-- title:
--   DS: lfa cp apply
-- statement:
--   The DS construction uses the lfa cp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L45-L48

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

theorem ReciprocityTheory.ChartRestriction.DS.lfa_cp_apply (x : Fin n × Fin n) (v : Fock n) :
    cpFock x.1 x.2 v = fockBasis n {finProdFinEquiv x} * v := by sorry
