-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_lgCurve_low
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lgCurve_low
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:38.035405+00:00
-- url     : https://prove2.me/theorems/80e11821-d9ba-488d-81bf-9958ee24e549
-- title:
--   PTb: coeff lg Curve low
-- statement:
--   The PTb construction uses the coeff lg Curve low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L255-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean#L255-L276

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lgCurve_low (G : LogFGL v d) {ga : Fin d → PowerSeries C} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ b, ∀ i < k, PowerSeries.coeff i (ga b) = 0) (a : Fin d) {j : ℕ} (hj : j < 2 * k) :
    PowerSeries.coeff j (G.lgCurve ga a) = PowerSeries.coeff j (ga a) := by sorry
