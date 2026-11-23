-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
-- name    : ReciprocityTheory.L2DbarEstimates.CkR.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:23.213318+00:00
-- url     : https://prove2.me/theorems/55afaf1a-2f33-460e-83c6-961173a2a4e9
-- title:
--   Ck R: comp
-- statement:
--   The Ck R construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L130-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L130-L137

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

theorem ReciprocityTheory.L2DbarEstimates.CkR.comp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (f : M → ℝ) (hf : CkR n z k f) :
    CkR n z k (fun x => φ (f x)) := by sorry
