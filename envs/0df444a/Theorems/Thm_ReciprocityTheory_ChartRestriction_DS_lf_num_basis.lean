-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_num_basis
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_num_basis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:18.174837+00:00
-- url     : https://prove2.me/theorems/200ad9f3-a8d2-4523-bfd0-5ecae11751f3
-- title:
--   DS: lf num basis
-- statement:
--   The DS construction uses the lf num basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L104-L111

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_num_basis (x : Fin n × Fin n) (S : Finset (Fin (n * n))) :
    cpFock x.1 x.2 (cmFock x.1 x.2 (fockBasis n S)) =
      if finProdFinEquiv x ∈ S then fockBasis n S else 0 := by sorry
