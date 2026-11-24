-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_four_zero
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimB.four_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:33.063988+00:00
-- url     : https://prove2.me/theorems/213ef17a-9845-4afe-ae0e-2ff0362f31c5
-- title:
--   Dim B: four zero
-- statement:
--   The Dim B construction uses the four zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean#L268-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean#L268-L334

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16

theorem ReciprocityTheory.ChartRestriction.G.I2.DimB.four_zero {q : ℕ} (hq : 0 < q) (h : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ h)
    (hp1 : ∀ l z, h (z + Pi.single l 1) = h z) (τ : Fin k → Fin k → ℂ) (C : Fin k → ℂ)
    (hqp : ∀ j z, h (z + τ j) = C j * cexp (2 * Real.pi * I * q * z j) * h z)
    (hc : ∀ m : Fin k → ℤ, (∀ l, 0 ≤ m l ∧ m l < q) → Av (Pm h m) 0 = 0) : h = 0 := by sorry
