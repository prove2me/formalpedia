-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rLinOnK_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.rLinOnK_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:42.900476+00:00
-- url     : https://prove2.me/theorems/279fc3b3-f114-49ab-a366-674864fcaf2c
-- title:
--   HW: r Lin On K zero
-- statement:
--   The HW construction uses the r Lin On K zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelCext.lean#L115-L116

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.rLinOnK_zero (ε : Fin n → Bool) : RLinOnK ε (0 : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) := by sorry
