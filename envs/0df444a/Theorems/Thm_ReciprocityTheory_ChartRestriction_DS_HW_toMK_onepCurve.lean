-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_toMK_onepCurve
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.toMK_onepCurve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:29.138173+00:00
-- url     : https://prove2.me/theorems/f0d24abf-64a6-4abf-90d1-0e675de45def
-- title:
--   HW: to MK onep Curve
-- statement:
--   The HW construction uses the to MK onep Curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean#L70-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.toMK_onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    toMK (onepCurve ε hX t) = NormedSpace.exp ((t : ℂ) • X) := by sorry
