-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_conjTranspose_eq_self_of_mem_noncompactPart
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.conjTranspose_eq_self_of_mem_noncompactPart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:39.185864+00:00
-- url     : https://prove2.me/theorems/2c27ee36-9e6d-5618-bdd4-831889c3574f
-- title:
--   S7: conj Transpose eq self of mem noncompact Part
-- statement:
--   The S7 construction uses the conj Transpose eq self of mem noncompact Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecSum.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecSum.lean#L26-L37

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.conjTranspose_eq_self_of_mem_noncompactPart {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) : Yᴴ = Y := by sorry
