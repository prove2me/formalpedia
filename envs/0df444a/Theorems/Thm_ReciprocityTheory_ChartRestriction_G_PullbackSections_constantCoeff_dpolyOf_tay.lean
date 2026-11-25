-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_dpolyOf_tay
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_dpolyOf_tay
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:39.85315+00:00
-- url     : https://prove2.me/theorems/7b2b2c49-94c2-47b6-99de-329eeea5b1c2
-- title:
--   Pullback Sections: constant Coeff dpoly Of tay
-- statement:
--   The Pullback Sections construction uses the constant Coeff dpoly Of tay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L273-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L273-L279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_dpolyOf_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} [Fintype ι]
    (u : ι → Fin g → ℂ) (P : MvPolynomial ι ℂ) :
    constantCoeff (DpolyOf (addF ℂ g) u P (tay θ 0)) = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 := by sorry
