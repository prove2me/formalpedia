-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_zero_off
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_zero_off
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:46.272313+00:00
-- url     : https://prove2.me/theorems/f53c4c05-c543-4af8-ba74-c41d6fb188e6
-- title:
--   F: cut zero off
-- statement:
--   The F construction uses the cut zero off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Cutoff.lean#L86-L93

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_zero_off {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (x : M)
    (hx : x ∉ tsupport (fun y => (η y : ℂ))) :
    η x = 0 ∧ (∀ j, d n z j (fun y => (η y : ℂ)) x = 0) ∧
      (∀ j, db n z j (fun y => (η y : ℂ)) x = 0) := by sorry
