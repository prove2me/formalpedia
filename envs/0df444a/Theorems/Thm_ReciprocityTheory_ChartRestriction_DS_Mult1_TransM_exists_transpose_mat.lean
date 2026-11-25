-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_TransM_exists_transpose_mat
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.TransM.exists_transpose_mat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:06.261749+00:00
-- url     : https://prove2.me/theorems/9f3365ee-21fe-5369-9401-0fc4ce8f371c
-- title:
--   Trans M: exists transpose mat
-- statement:
--   The Trans M construction uses the exists transpose mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/JTransMA.lean#L233-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/JTransMA.lean#L233-L301

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_JTransMA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1
open ReciprocityTheory.ChartRestriction.DS.Mult1.TransM
variable {S : Type} [Fintype S] [DecidableEq S]

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.TransM.exists_transpose_mat (m : Matrix S S ℂ) (hm : mᴴ * m = 1) (w : S → ℂ) (hw : ∀ s, conj (w s) = w s) :
    ∃ U : Matrix S S ℂ, Uᴴ * U = 1 ∧ U *ᵥ w = w ∧ m.map (starRingEnd ℂ) * U * m = U := by sorry
