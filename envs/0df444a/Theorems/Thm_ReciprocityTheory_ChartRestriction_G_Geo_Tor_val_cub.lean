-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_cub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:38.861803+00:00
-- url     : https://prove2.me/theorems/7248c99b-d1cb-44d8-b6ba-d3f02c8da6ee
-- title:
--   Tor: val cub
-- statement:
--   The Tor construction uses the val cub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L121-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
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
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_cub {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J : (T'.left ⟶ G.left) → L.L.ι} (hJ : Good L.L z J)
    (x x' y : T ⟶ G) : val (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left) ρ.left z J =
      cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by sorry
