-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_f0K
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.hasDerivAt_f0K
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:10.945899+00:00
-- url     : https://prove2.me/theorems/c8e746c7-8df7-535b-b779-db31fac7f1dd
-- title:
--   HW: has Deriv At f0 K
-- statement:
--   The HW construction uses the has Deriv At f0 K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L113-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean#L113-L134

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.hasDerivAt_f0K (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (x : KG ε) :
    HasDerivAt (fun t : ℝ => f0K ε m (x * kcurve ε X t)) (fderiv ℂ (f0 ε m) (toMK x) (toMK x * X)) 0 := by sorry
