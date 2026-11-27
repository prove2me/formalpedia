-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_tail
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_tail
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:53.24339+00:00
-- url     : https://prove2.me/theorems/e42f16ff-5beb-4343-8a54-099a12d9b038
-- title:
--   I2: cab tail
-- statement:
--   The I2 construction uses the cab tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L298-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L298-L359

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

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_tail (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) {κ : Type}
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (g' : ℕ) (hN : Module.finrank ℝ W = 2 * g') (U : κ → W) (δ k : ℝ) (hδ : 0 < δ) (hk : 0 < k)
    (hsep : ∀ a b, a ≠ b → δ ≤ ‖U a - U b‖) (hlow : ∀ a, δ ≤ ‖U a‖)
    (hbig : 2 * (g' : ℝ) + 1 ≤ k * δ ^ 2) :
    Summable (fun a => Real.exp (-(k * ‖U a‖ ^ 2))) ∧
      ∑' a, Real.exp (-(k * ‖U a‖ ^ 2)) ≤ 2 * 9 ^ g' * Real.exp (-(k * δ ^ 2)) := by sorry
