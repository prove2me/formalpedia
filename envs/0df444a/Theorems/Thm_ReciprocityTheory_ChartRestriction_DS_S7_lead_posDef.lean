-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_posDef
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.lead_posDef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:31.598056+00:00
-- url     : https://prove2.me/theorems/1c45b6c2-f4e6-4b14-8780-bf64de8d6f39
-- title:
--   S7: lead pos Def
-- statement:
--   The S7 construction uses the lead pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/Minors.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/Minors.lean#L84-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.lead_posDef {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (i : ℕ) (hi : i ≤ n) :
    0 < (lead i x).re ∧ (lead i x).im = 0 := by sorry
