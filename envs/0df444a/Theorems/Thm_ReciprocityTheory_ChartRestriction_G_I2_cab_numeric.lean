-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_numeric
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_numeric
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:30.94963+00:00
-- url     : https://prove2.me/theorems/19a667e0-dd69-4214-87fc-580f6f961a22
-- title:
--   I2: cab numeric
-- statement:
--   The I2 construction uses the cab numeric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L219-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L219-L288

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

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_numeric (c G gA g' dst : ℕ) (q t0 : ℝ) (hq : 2 ≤ q) (hG : G ≤ gA) (hg' : 2 * g' ≤ dst)
    (hC5 : 4 * c * (7 + Real.log (q * c)) + dst + 1 ≤ t0) (hC6 : gA * Real.log 2 ≤ t0) :
    Real.sqrt (12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c) *
        (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
        (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * c.factorial := by sorry
