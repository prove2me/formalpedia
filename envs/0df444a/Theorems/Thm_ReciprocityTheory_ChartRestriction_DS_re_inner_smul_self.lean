-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_re_inner_smul_self
-- name    : ReciprocityTheory.ChartRestriction.DS.re_inner_smul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:21.621971+00:00
-- url     : https://prove2.me/theorems/d95b871a-7cd2-4049-a269-5c31f7952f4f
-- title:
--   DS: re inner smul self
-- statement:
--   The DS construction uses the re inner smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L54-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.re_inner_smul_self (c : ℝ) (x : M) :
    RCLike.re (inner ℂ ((c : ℂ) • x) x) = c * ‖x‖ ^ 2 := by sorry
