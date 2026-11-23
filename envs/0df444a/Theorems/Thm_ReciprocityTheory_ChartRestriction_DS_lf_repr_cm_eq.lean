-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_repr_cm_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_repr_cm_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:15.414238+00:00
-- url     : https://prove2.me/theorems/095a60c4-ba80-4f93-a2b9-3e68762a1679
-- title:
--   DS: lf repr cm eq
-- statement:
--   The DS construction uses the lf repr cm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L113-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L113-L137

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_repr_cm_eq (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    (fockBasis n).repr (cmFock x.1 x.2 (fockBasis n S)) T =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n T)) S := by sorry
