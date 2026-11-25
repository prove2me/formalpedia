-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_ofReal_le
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_ofReal_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:28.373432+00:00
-- url     : https://prove2.me/theorems/31fcd31d-4156-4e87-a018-fe170cc99363
-- title:
--   F: loc of Real le
-- statement:
--   The F construction uses the loc of Real le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L497-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L497-L502

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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

theorem ReciprocityTheory.L2DbarEstimates.F.loc_ofReal_le {N : ℕ} (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) (a : ℝ)
    (h : a ≤ N * ∑ i, b i) : ENNReal.ofReal a ≤ N * ∑ i, ENNReal.ofReal (b i) := by sorry
