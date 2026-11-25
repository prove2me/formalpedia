-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_nuNext_tele
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.nuNext_tele
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:49.226903+00:00
-- url     : https://prove2.me/theorems/15d03870-725c-55fc-ac44-6c13d0c57b79
-- title:
--   S7: nu Next tele
-- statement:
--   The S7 construction uses the nu Next tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecSum.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecSum.lean#L73-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
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

theorem ReciprocityTheory.ChartRestriction.DS.S7.nuNext_tele (ν : Fin n → ℝ) {a b : Fin n} (hba : b < a) :
    ∑ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) = ν b - ν a := by sorry
