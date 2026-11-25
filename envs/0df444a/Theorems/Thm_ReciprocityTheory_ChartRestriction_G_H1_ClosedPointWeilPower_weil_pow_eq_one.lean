-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_ClosedPointWeilPower_weil_pow_eq_one
-- name    : ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.weil_pow_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:41.095025+00:00
-- url     : https://prove2.me/theorems/f226a84e-558b-405b-8446-2613a5052895
-- title:
--   Closed Point Weil Power: weil pow eq one
-- statement:
--   The Closed Point Weil Power construction uses the weil pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ClosedPointWeilPower.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ClosedPointWeilPower.lean#L52-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.weil_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by sorry
