-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.toMK_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:27.639835+00:00
-- url     : https://prove2.me/theorems/56b276b2-e3ea-4b82-9310-e961d2260db9
-- title:
--   S7: to MK facts
-- statement:
--   The S7 construction uses the to MK facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ExpInPPosDef.lean#L50-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
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
variable {ε : Fin n → Bool}
open PolarDecomposition

theorem ReciprocityTheory.ChartRestriction.DS.S7.toMK_facts (k : KG ε) : (toMK k)ᴴ * toMK k = 1 ∧ toMK k * (toMK k)ᴴ = 1 ∧
    toMK k * Jm ε = Jm ε * toMK k := by sorry
