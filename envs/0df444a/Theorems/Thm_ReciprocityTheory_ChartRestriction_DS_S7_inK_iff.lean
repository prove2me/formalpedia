-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inK_iff
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.inK_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:33.336761+00:00
-- url     : https://prove2.me/theorems/cc731862-ee10-4555-ade4-d0e33f8e5b3b
-- title:
--   S7: in K iff
-- statement:
--   The S7 construction uses the in K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/KFacts.lean#L59-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/KFacts.lean#L59-L98

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by sorry
