-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_hasDerivAt_A
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hwmf_hasDerivAt_A
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:34.519583+00:00
-- url     : https://prove2.me/theorems/7b11dc9f-0200-541f-bca1-d22a18287a65
-- title:
--   HW: hwmf has Deriv At A
-- statement:
--   The HW construction uses the hwmf has Deriv At A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L102-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ReciprocityTheory.ChartRestriction.DS.HW.hwmf_hasDerivAt_A (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => Y * NormedSpace.exp ((t : ℂ) • X)) (Y * X) 0 := by sorry
