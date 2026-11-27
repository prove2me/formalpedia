-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_PeriodicValuation_all_of_periodic
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.PeriodicValuation.all_of_periodic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:27:20.458419+00:00
-- url     : https://prove2.me/theorems/086c7669-3957-4a27-9740-5706e3411b33
-- title:
--   Periodic Valuation: all of periodic
-- statement:
--   The Periodic Valuation construction uses the all of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PeriodicValuation.lean#L30-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PeriodicValuation.lean#L30-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ConstBFMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PeriodicValuation
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
open ReciprocityTheory.ChartRestriction.G.DVR.PeriodicValuation

theorem ReciprocityTheory.ChartRestriction.G.DVR.PeriodicValuation.all_of_periodic {P : ℚ → Prop} (hmono : ∀ r r' : ℚ, r' ≤ r → P r → P r') {d : ℚ} (hd : d ≠ 0)
    (hper : ∀ r, P r ↔ P (r + d)) (r₁ r₂ : ℚ) (h : P r₁) : P r₂ := by sorry
