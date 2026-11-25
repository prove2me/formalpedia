-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_wd_wdb_ofReal
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rm_wd_wdb_ofReal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:01:03.293695+00:00
-- url     : https://prove2.me/theorems/ad801e74-6fb2-42c9-a509-9292082e4aae
-- title:
--   Y: rm wd wdb of Real
-- statement:
--   The Y construction uses the rm wd wdb of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L186-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L186-L208

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.rm_wd_wdb_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (j k : Fin n) :
    wd n j (wdb n k (fun x => (F x : ℂ))) y =
      (((fderiv ℝ (fderiv ℝ F) y (bas n j) (bas n k) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ (fderiv ℝ F) y (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (bas n k) : ℝ) : ℂ)
        + ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)) / 4 := by sorry
