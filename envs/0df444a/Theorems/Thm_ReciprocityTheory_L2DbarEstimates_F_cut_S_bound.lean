-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_S_bound
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_S_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:32.275874+00:00
-- url     : https://prove2.me/theorems/1c492cc4-0a3d-5f5c-b4d9-cfdaf84a542a
-- title:
--   F: cut S bound
-- statement:
--   The F construction uses the cut S bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L327-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L327-L337

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_S_bound {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ)
    (fx : V n) (x : M) :
    ‖∑ j, d n z j (fun y => (η y : ℂ)) x * fx j‖ ^ 2 ≤ dbarSq n z (fun y => (η y : ℂ)) x * ‖fx‖ ^ 2 := by sorry
