-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_repr_cp_star
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_repr_cp_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:51.454868+00:00
-- url     : https://prove2.me/theorems/7d593e1f-3fac-4267-9522-35af22974fcf
-- title:
--   DS: lf repr cp star
-- statement:
--   The DS construction uses the lf repr cp star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L139-L147

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_repr_cp_star (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    star ((fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T) =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T := by sorry
