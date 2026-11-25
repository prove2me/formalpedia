-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_cpart_bdPart_of_inK
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.cpart_bdPart_of_inK
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:00.358615+00:00
-- url     : https://prove2.me/theorems/b8a437f8-633f-42a8-9516-12f2370faac7
-- title:
--   HW: cpart bd Part of in K
-- statement:
--   The HW construction uses the cpart bd Part of in K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L53-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.cpart_bdPart_of_inK (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    cpart1 ε (bdPart ε X) = X ∧ cpart2 ε (bdPart ε X) = 0 := by sorry
