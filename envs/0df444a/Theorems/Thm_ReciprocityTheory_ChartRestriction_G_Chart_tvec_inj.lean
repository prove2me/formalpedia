-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:08.323698+00:00
-- url     : https://prove2.me/theorems/135c6388-01c6-54d7-8096-b86445ac27d9
-- title:
--   Chart: tvec inj
-- statement:
--   The Chart construction uses the tvec inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L21-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {Gx : Over (Spec (CommRingCat.of R))} [GrpObj Gx] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ Gx} (hx : IsUnivChart Gx n x)
include hx

theorem ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj {c c' : Fin n → R} (h : tvec (x := x) c = tvec (x := x) c') : c = c' := by sorry
