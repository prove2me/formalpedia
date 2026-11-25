-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_extend_support_subset
-- name    : ReciprocityTheory.L2DbarEstimates.F.extend_support_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:02:32.975959+00:00
-- url     : https://prove2.me/theorems/b46b352c-8193-5567-9a8d-038a14449498
-- title:
--   F: extend support subset
-- statement:
--   The F construction uses the extend support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Extend.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Extend.lean#L11-L17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Extend
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

theorem ReciprocityTheory.L2DbarEstimates.F.extend_support_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (q : M)
    (hq : e.source.indicator (G ∘ e) q ≠ 0) : q ∈ e.symm '' tsupport G := by sorry
