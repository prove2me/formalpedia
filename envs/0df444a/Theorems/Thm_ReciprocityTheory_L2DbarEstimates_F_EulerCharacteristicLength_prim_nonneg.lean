-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_prim_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.prim_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:44.723013+00:00
-- url     : https://prove2.me/theorems/b9d042af-9aca-435c-85c8-1782b0648b62
-- title:
--   Euler Characteristic Length: prim nonneg
-- statement:
--   The Euler Characteristic Length construction uses the prim nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/PrimZeroOfNonpos.lean#L34-L38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
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
open ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength

theorem ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.prim_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, x ≤ 0 → f x = 0) (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ prim f t := by sorry
