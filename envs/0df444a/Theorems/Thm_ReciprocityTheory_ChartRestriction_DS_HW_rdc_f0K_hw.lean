-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rdc_f0K_hw
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.rdc_f0K_hw
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:15.156803+00:00
-- url     : https://prove2.me/theorems/599e5b4d-7f86-5e10-8779-9e74711229a3
-- title:
--   HW: rdc f0 K hw
-- statement:
--   The HW construction uses the rdc f0 K hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L367-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L367-L376

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.rdc_f0K_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) (x : KG ε) : rdc ε (Matrix.single a b 1) (f0K ε m) x = 0 := by sorry
