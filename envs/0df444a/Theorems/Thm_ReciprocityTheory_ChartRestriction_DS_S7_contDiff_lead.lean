-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiff_lead
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.contDiff_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:33.065839+00:00
-- url     : https://prove2.me/theorems/c3864a30-c43f-4ca7-bdec-c41b91227a6b
-- title:
--   S7: cont Diff lead
-- statement:
--   The S7 construction uses the cont Diff lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L20-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.contDiff_lead (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (lead (n := n) i) := by sorry
