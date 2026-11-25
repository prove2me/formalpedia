-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_isKHWVec_iff
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_isKHWVec_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:13.905265+00:00
-- url     : https://prove2.me/theorems/1cb35f5a-0021-41db-9b1a-a8b6793319ee
-- title:
--   HW: pieri St is KHWVec iff
-- statement:
--   The HW construction uses the pieri St is KHWVec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L23-L25

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_isKHWVec_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) (v : W) :
    IsKHWVec ε E μ v ↔ Formalism.REAL.KHighest ε E μ v := by sorry
