-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_twist_toMK_inj
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.twist_toMK_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:15.574836+00:00
-- url     : https://prove2.me/theorems/ab1dd744-3c36-4646-a5b4-33b85d284741
-- title:
--   HW: twist to MK inj
-- statement:
--   The HW construction uses the twist to MK inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelTwist.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelTwist.lean#L28-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.twist_toMK_inj {ε : Fin n → Bool} {k k' : KG ε} (h : toMK k = toMK k') : k = k' := by sorry
