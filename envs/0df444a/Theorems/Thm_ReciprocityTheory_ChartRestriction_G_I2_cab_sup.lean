-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_sup
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:08.550679+00:00
-- url     : https://prove2.me/theorems/fd2c76f5-abc5-4bb8-a228-357387335964
-- title:
--   I2: cab sup
-- statement:
--   The I2 construction uses the cab sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L120-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L120-L161

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
open MeasureTheory
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_sup (hS : GSupStatement) (Y : GT ι) (q c : ℕ) (hq : 2 ≤ q) (R0 : ℝ) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (h90 : 90 * (Fintype.card ι : ℝ) ≤ R0 ^ 2) (β : EuclideanSpace ℂ ι → ℂ) (hβ : β ∈ Y.Sec q)
    (hl2 : Y.l2 q β ≤ 6 * (c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ Fintype.card ι))
    (w : EuclideanSpace ℂ ι) :
    Y.ptN2 q β w ≤ 12 * (5.12 : ℝ) ^ Fintype.card ι * c.factorial * (2 / (q * Real.pi)) ^ c := by sorry
