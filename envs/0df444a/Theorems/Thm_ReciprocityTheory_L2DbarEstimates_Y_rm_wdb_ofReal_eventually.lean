-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_wdb_ofReal_eventually
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rm_wdb_ofReal_eventually
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:01.558007+00:00
-- url     : https://prove2.me/theorems/9f105209-9413-5679-8e38-3b80f667e568
-- title:
--   Y: rm wdb of Real eventually
-- statement:
--   The Y construction uses the rm wdb of Real eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L162-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L162-L171

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

theorem ReciprocityTheory.L2DbarEstimates.Y.rm_wdb_ofReal_eventually (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by sorry
