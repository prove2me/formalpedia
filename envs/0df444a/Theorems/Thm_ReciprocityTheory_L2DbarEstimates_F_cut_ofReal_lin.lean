-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ofReal_lin
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_ofReal_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:48.251714+00:00
-- url     : https://prove2.me/theorems/74c2db69-895b-5297-8b5d-d9464775790c
-- title:
--   F: cut of Real lin
-- statement:
--   The F construction uses the cut of Real lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L71-L76

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_ofReal_lin (p q a b c : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : c ≤ p * a + q * b) :
    ENNReal.ofReal c ≤ ENNReal.ofReal p * ENNReal.ofReal a + ENNReal.ofReal q * ENNReal.ofReal b := by sorry
