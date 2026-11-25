-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jet_product_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.jet_product_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:45.156324+00:00
-- url     : https://prove2.me/theorems/7bef53cf-8ef3-5d3c-8b42-2a28dea838c3
-- title:
--   I2: jet product le
-- statement:
--   The I2 construction uses the jet product le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusB.lean#L115-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusB.lean#L115-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Real

theorem ReciprocityTheory.ChartRestriction.G.I2.jet_product_le (q c dK gA dst : ℕ) (hq : 1 ≤ q) {n U t0 Bsq : ℝ} (hn : 1 ≤ n) (hU0 : 0 ≤ U)
    (hU : 2 * π * U ≤ 1.5 * n) (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0)
    (hB : Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst) :
    (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by sorry
