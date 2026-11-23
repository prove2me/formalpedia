-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_of_gm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:25.243356+00:00
-- url     : https://prove2.me/theorems/463213d8-4cc5-4121-a734-306b8a9ac28d
-- title:
--   Tor: is Gen of gm
-- statement:
--   The Tor construction uses the is Gen of gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean#L113-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean#L113-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_of_gm {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (h : ∀ (y : Y) (j j' : K → M.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart M φ j' →
      gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart M φ j') (t.s j')) : t.IsGen := by sorry
