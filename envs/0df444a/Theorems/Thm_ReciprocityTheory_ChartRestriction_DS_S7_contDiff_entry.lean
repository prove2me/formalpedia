-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiff_entry
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.contDiff_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:04.736817+00:00
-- url     : https://prove2.me/theorems/462c4827-4cf8-4e3f-a822-0322cf1d3eba
-- title:
--   S7: cont Diff entry
-- statement:
--   The S7 construction uses the cont Diff entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L16-L18

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.contDiff_entry (a b : Fin n) {m : ℕ∞ω} :
    ContDiff ℂ m (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by sorry
