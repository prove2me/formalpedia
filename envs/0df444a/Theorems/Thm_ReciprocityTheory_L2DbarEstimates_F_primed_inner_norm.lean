-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_primed_inner_norm
-- name    : ReciprocityTheory.L2DbarEstimates.F.primed_inner_norm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:54.026838+00:00
-- url     : https://prove2.me/theorems/c1f4e5eb-a0a7-4107-b452-ee463a6f092d
-- title:
--   F: primed inner norm
-- statement:
--   The F construction uses the primed inner norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Primed.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Primed.lean#L43-L48

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Primed
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

theorem ReciprocityTheory.L2DbarEstimates.F.primed_inner_norm (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (F0 : M → ℂ)
    (g : M → V n) (x : M) :
    ‖⟪dbarF n z F0 x, g x⟫_ℂ‖ = ‖dbarDot n z F0 x (fun j => g x j)‖ := by sorry
