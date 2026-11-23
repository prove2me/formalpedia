-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pullGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:05.899564+00:00
-- url     : https://prove2.me/theorems/2774eb4d-470a-4678-9ab9-9f971bd0b98d
-- title:
--   Tor: gm pull Gen
-- statement:
--   The Tor construction uses the gm pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean#L196-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/BCTools.lean#L196-L207

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X Y Y' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pullGen {Z Z' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (r : Z' ⟶ Z) (z : Z') (j : K → L.ι)
    (hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) j) :
    gm r z (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by sorry
