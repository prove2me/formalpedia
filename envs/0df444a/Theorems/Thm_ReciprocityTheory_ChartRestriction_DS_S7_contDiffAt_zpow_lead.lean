-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_zpow_lead
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.contDiffAt_zpow_lead
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:44:30.775893+00:00
-- url     : https://prove2.me/theorems/536f6970-9c3c-4e74-8ba7-8525b352f615
-- title:
--   S7: cont Diff At zpow lead
-- statement:
--   The S7 construction uses the cont Diff At zpow lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiCasA.lean#L33-L40

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.contDiffAt_zpow_lead (i : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : lead i z ≠ 0)
    {m : ℕ∞ω} : ContDiffAt ℂ m (fun w => lead i w ^ k) z := by sorry
