-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_cext_of_inK
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.cext_of_inK
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:11.040067+00:00
-- url     : https://prove2.me/theorems/fe54834c-d583-49af-bde9-8166e0bda1e7
-- title:
--   HW: cext of in K
-- statement:
--   The HW construction uses the cext of in K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L148-L155

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.cext_of_inK (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : cext ε A X = A X := by sorry
