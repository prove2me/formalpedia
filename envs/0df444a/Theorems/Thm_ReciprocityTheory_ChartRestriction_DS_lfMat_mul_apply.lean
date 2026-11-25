-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfMat_mul_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.lfMat_mul_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:18.242912+00:00
-- url     : https://prove2.me/theorems/62ac0f82-2b6b-5c89-a112-6f815eea6ff2
-- title:
--   DS: lf Mat mul apply
-- statement:
--   The DS construction uses the lf Mat mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L108-L119

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
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

theorem ReciprocityTheory.ChartRestriction.DS.lfMat_mul_apply (ε : Fin n → Bool) (a b c d : Fin n) (T S : LfIdx ε) :
    (lfMat ε a b * lfMat ε c d) T S = (lfMatFull ε a b * lfMatFull ε c d) T.1 S.1 := by sorry
