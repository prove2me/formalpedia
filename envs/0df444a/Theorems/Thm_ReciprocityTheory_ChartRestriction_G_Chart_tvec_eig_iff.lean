-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:17.031695+00:00
-- url     : https://prove2.me/theorems/2b520b0b-6122-48f6-9092-6dbb7eb26ae1
-- title:
--   Chart: tvec eig iff
-- statement:
--   The Chart construction uses the tvec eig iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L44-L47

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff (e : Gx ⟶ Gx) [IsMonHom e] (c : Fin n → R) (s : R) :
    tvec (x := x) c ≫ e = spMap (scaleD s) ≫ tvec (x := x) c ↔ tmap hx e c = s • c := by sorry
