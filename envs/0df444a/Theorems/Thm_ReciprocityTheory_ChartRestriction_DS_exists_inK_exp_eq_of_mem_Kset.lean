-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_inK_exp_eq_of_mem_Kset
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_inK_exp_eq_of_mem_Kset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:43.306302+00:00
-- url     : https://prove2.me/theorems/b683e95a-8ef9-4125-a23c-b30e681e3d26
-- title:
--   DS: exists in K exp eq of mem Kset
-- statement:
--   The DS construction uses the exists in K exp eq of mem Kset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ExistsExpEqOfMemKset.lean#L22-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ExistsExpEqOfMemKset.lean#L22-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open scoped Matrix.Norms.L2Operator

theorem ReciprocityTheory.ChartRestriction.DS.exists_inK_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k := by sorry
