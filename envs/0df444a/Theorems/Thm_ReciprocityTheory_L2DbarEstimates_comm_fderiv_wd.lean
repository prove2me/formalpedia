-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_fderiv_wd
-- name    : ReciprocityTheory.L2DbarEstimates.comm_fderiv_wd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:18.747161+00:00
-- url     : https://prove2.me/theorems/1a52c325-da3e-4cae-99f1-3ffc561a5907
-- title:
--   L2 Dbar Estimates: comm fderiv wd
-- statement:
--   The L2 Dbar Estimates construction uses the comm fderiv wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L17-L32

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

theorem ReciprocityTheory.L2DbarEstimates.comm_fderiv_wd {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j : Fin n) (v : V n) :
    fderiv ℝ (wd n j g) y v = (fderiv ℝ (fderiv ℝ g) y v (bas n j)
      - Complex.I * fderiv ℝ (fderiv ℝ g) y v (Complex.I • bas n j)) * (2 : ℂ)⁻¹ := by sorry
