-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:30.940806+00:00
-- url     : https://prove2.me/theorems/8add4aec-c4be-4f6d-b122-d82bcbb47cdd
-- title:
--   Ck: mul
-- statement:
--   The Ck construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L100-L102

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Ck.mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℂ) (hf : Ck n z k f) (hg : Ck n z k g) :
    Ck n z k (fun x => f x * g x) := by sorry
