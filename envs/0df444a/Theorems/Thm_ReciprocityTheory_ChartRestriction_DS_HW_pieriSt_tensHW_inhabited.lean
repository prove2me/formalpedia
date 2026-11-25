-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_tensHW_inhabited
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_tensHW_inhabited
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:37.044306+00:00
-- url     : https://prove2.me/theorems/59264839-4f6a-4740-b699-d5214263322f
-- title:
--   HW: pieri St tens HW inhabited
-- statement:
--   The HW construction uses the pieri St tens HW inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L53-L69

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_tensHW_inhabited {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.KRel ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KUnit ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KHighest ε (0 : Fin n → Fin n → Module.End ℂ ℂ) 0 (1 : ℂ) ∧
    Formalism.REAL.kSpan ε (0 : Fin n → Fin n → Module.End ℂ ℂ) (1 : ℂ) = ⊤ ∧
    Formalism.REAL.KRel ε (stdM n) ∧
    (∀ a, stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ)) := by sorry
