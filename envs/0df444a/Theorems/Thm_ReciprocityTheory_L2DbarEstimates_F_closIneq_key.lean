-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_closIneq_key
-- name    : ReciprocityTheory.L2DbarEstimates.F.closIneq_key
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:02.058546+00:00
-- url     : https://prove2.me/theorems/b79ce310-9e11-5ae8-8029-1311585fe86a
-- title:
--   F: clos Ineq key
-- statement:
--   The F construction uses the clos Ineq key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Closure.lean#L27-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Closure.lean#L27-L48

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure
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

theorem ReciprocityTheory.L2DbarEstimates.F.closIneq_key {X P Q : ℝ≥0∞} (hQ : Q ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → X ≤ P + ENNReal.ofReal δ * Q) : X ≤ P := by sorry
