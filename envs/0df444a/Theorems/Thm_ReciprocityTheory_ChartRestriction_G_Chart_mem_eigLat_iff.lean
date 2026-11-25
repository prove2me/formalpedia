-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_mem_eigLat_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:21.050123+00:00
-- url     : https://prove2.me/theorems/eb73b45f-5fb4-4bb7-a1b1-8004ae4ffb56
-- title:
--   Chart: mem eig Lat iff
-- statement:
--   The Chart construction uses the mem eig Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L39-L42

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff {O : Type} (act : O → (Gx ⟶ Gx)) [∀ a, IsMonHom (act a)] (χ : O → R) (c : Fin n → R) :
    c ∈ eigLat hx act χ ↔ ∀ a, tmap hx (act a) c = χ a • c := by sorry
