-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ros
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ros
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:04.752799+00:00
-- url     : https://prove2.me/theorems/3e5dc459-4061-4351-8f12-c1c4ac9f46f6
-- title:
--   Tor: exists ros
-- statement:
--   The Tor construction uses the exists ros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L169-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean#L169-L277

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ros (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : RosatiAdj A L f g) : ∃ u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) := by sorry
