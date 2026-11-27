-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_arith
-- name    : ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.arith
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:03.680867+00:00
-- url     : https://prove2.me/theorems/e2678239-e3be-5b75-b85a-158288c1a214
-- title:
--   Levi Form Quadratic Sums: arith
-- statement:
--   The Levi Form Quadratic Sums construction uses the arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeD.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeD.lean#L31-L35

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n d : ℕ} {p : V n → V d} {U : Set (V n)}

theorem ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.arith {a b t L s : ℝ} (ha : 0 ≤ a) (hab : 0 ≤ a + t * b) (hL : 0 ≤ L) (hs0 : 0 ≤ s)
    (hs : s ≤ t * L) : 0 ≤ a * L + b * s := by sorry
