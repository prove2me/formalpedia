-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_eq_two_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hs_eq_two_lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:03.124411+00:00
-- url     : https://prove2.me/theorems/5c63dec7-11d7-5c5c-abdc-7067c1abd006
-- title:
--   S7: hs eq two lower
-- statement:
--   The S7 construction uses the hs eq two lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecSum.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecSum.lean#L44-L65

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.hs_eq_two_lower {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    hs Y = 2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by sorry
