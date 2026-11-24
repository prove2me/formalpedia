-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_stdM_diag
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_stdM_diag
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:23.847275+00:00
-- url     : https://prove2.me/theorems/0694ddd1-3dcd-4f6a-b820-1087e3fecd8d
-- title:
--   HW: pieri St std M diag
-- statement:
--   The HW construction uses the pieri St std M diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L42-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_StTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_stdM_diag {n : ℕ} (a : Fin n) :
    stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ) := by sorry
