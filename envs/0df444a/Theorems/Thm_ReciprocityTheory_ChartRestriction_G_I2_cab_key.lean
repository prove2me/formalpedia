-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_key
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_key
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:22.441861+00:00
-- url     : https://prove2.me/theorems/ef9575c8-2436-4ad2-966b-4a4c86f52e6f
-- title:
--   I2: cab key
-- statement:
--   The I2 construction uses the cab key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L175-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L175-L217

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_key (c gA : ℕ) (q t0 : ℝ) (hq : 2 ≤ q) (dst : ℝ) (hd : 0 ≤ dst)
    (hC5 : 4 * c * (7 + Real.log (q * c)) + dst + 1 ≤ t0) (hC6 : gA * Real.log 2 ≤ t0) :
    (5.12 : ℝ) ^ gA * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
      Real.exp (-((Real.pi - 2) * t0)) ≤ 4 ^ gA := by sorry
