-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_small
-- name    : ReciprocityTheory.L2DbarEstimates.F.unwBack_small
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:24.043163+00:00
-- url     : https://prove2.me/theorems/5d5796a0-96e6-5ea1-a80a-2b5660b37449
-- title:
--   F: unw Back small
-- statement:
--   The F construction uses the unw Back small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L11-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L11-L42

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.unwBack_small (δ : ℝ≥0∞) (hδ : 0 < δ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ' : ℝ≥0∞, 0 < δ' ∧ ∀ a b : ℝ≥0∞, a < δ' → b < δ' → ENNReal.ofReal C * (a + b) < δ := by sorry
