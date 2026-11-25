-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_bound
-- name    : ReciprocityTheory.L2DbarEstimates.F.unwBack_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:05.50447+00:00
-- url     : https://prove2.me/theorems/23ab2f82-4422-4d2d-87e2-958c29fac4be
-- title:
--   F: unw Back bound
-- statement:
--   The F construction uses the unw Back bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L44-L50

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
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

theorem ReciprocityTheory.L2DbarEstimates.F.unwBack_bound {M : Type*} [TopologicalSpace M] (K : Set M) (hK : IsCompact K) (F : M → ℝ)
    (hF : Continuous F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, F x ≤ C := by sorry
