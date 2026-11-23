-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ros_add
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ros_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:13.051798+00:00
-- url     : https://prove2.me/theorems/4428b2d5-13d0-4110-9bc9-5bfd118c11a1
-- title:
--   Tor: ros add
-- statement:
--   The Tor construction uses the ros add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L281-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L281-L365

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
variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.ros_add (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') := by sorry
