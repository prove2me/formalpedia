-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_tail_deriv
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_tail_deriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:03.898042+00:00
-- url     : https://prove2.me/theorems/1316978c-88a8-5a08-a945-ebfa32daa4c7
-- title:
--   I2: cab tail deriv
-- statement:
--   The I2 construction uses the cab tail deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L176-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L176-L225

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
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

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_tail_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} (R : V → ℂ) (hR : Differentiable ℂ R) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (q : ℝ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B) (u : κ → ℝ)
    (hsum : Summable (fun a => Real.exp (-(Real.pi / 2 * q * u a ^ 2))))
    (hbd : ∀ v, ‖R v‖ ≤ B * ∑' a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
      2 * q * Real.pi * ‖v‖ * u a)) :
    ‖iteratedFDeriv ℂ c R 0 x‖ ≤ B * (q * (c + 1)) ^ ((c : ℝ) / 2) *
      Real.exp (5 * Real.pi * c / 2) * ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by sorry
