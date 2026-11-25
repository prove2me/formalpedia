-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefD_Am_exp
-- name    : ReciprocityTheory.ChartRestriction.DS.coefD_Am_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:27.993572+00:00
-- url     : https://prove2.me/theorems/94b186ca-b2d5-58e7-a6c3-a9ed85e63196
-- title:
--   DS: coef D Am exp
-- statement:
--   The DS construction uses the coef D Am exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefDTensActPow.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefDTensActPow.lean#L21-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.coefD_Am_exp (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    coefAm dual (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp ((s : ℂ) • coefBm dual X) := by sorry
