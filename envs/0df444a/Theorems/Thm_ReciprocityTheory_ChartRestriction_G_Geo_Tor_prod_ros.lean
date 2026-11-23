-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_ros
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:22:14.306772+00:00
-- url     : https://prove2.me/theorems/68762bf7-6715-4ed4-acaf-bec33b74eda8
-- title:
--   Tor: prod ros
-- statement:
--   The Tor construction uses the prod ros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L151-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L151-L167

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_ros (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ i, h ((lift x y).left ≫ rosatiφ A f g i) ^ rosatiε i =
      h ((x ≫ f) * y).left * (h (x ≫ f).left)⁻¹ * (h y.left)⁻¹ * (h (x * (y ≫ g)).left)⁻¹ * h x.left * h (y ≫ g).left := by sorry
