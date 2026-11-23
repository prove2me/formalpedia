-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_muK_rightInvariant
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.muK_rightInvariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:18.299794+00:00
-- url     : https://prove2.me/theorems/2f466755-215f-45ef-877d-d126606c3b65
-- title:
--   S7: mu K right Invariant
-- statement:
--   The S7 construction uses the mu K right Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/KFacts.lean#L37-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/KFacts.lean#L37-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
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

theorem ReciprocityTheory.ChartRestriction.DS.S7.muK_rightInvariant (ε : Fin n → Bool) : (muK ε).IsMulRightInvariant := by sorry
