-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.onep_KG_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:38.588149+00:00
-- url     : https://prove2.me/theorems/7879462c-e1dd-42ac-8ac3-b1642a9a97e6
-- title:
--   HW: onep KG ext
-- statement:
--   The HW construction uses the onep KG ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/OneParam.lean#L77-L82

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.onep_KG_ext {ε : Fin n → Bool} {g h : KG ε} (hgh : toMK g = toMK h) : g = h := by sorry
