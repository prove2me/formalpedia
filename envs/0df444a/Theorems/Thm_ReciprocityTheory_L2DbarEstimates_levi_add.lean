-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_add
-- name    : ReciprocityTheory.L2DbarEstimates.levi_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:09.519419+00:00
-- url     : https://prove2.me/theorems/24654f2a-51f1-4cd9-b410-457d61518388
-- title:
--   L2 Dbar Estimates: levi add
-- statement:
--   The L2 Dbar Estimates construction uses the levi add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L161-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L161-L173

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.levi_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ps : M → ℝ) (hph : CkR n z 2 ph) (hps : CkR n z 2 ps) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ph y + ps y) x ξ = Levi n z ph x ξ + Levi n z ps x ξ := by sorry
