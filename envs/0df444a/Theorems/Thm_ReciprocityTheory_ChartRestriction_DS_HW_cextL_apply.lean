-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_cextL_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.cextL_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:09.309194+00:00
-- url     : https://prove2.me/theorems/34fcfec7-6864-5572-bd13-666943739f6e
-- title:
--   HW: cext L apply
-- statement:
--   The HW construction uses the cext L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L163-L164

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem ReciprocityTheory.ChartRestriction.DS.HW.cextL_apply (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cextL ε A hA Z = cext ε A Z := by sorry
