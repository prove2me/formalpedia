-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_O__pull_be9eb376d61b
-- name    : P2M_GlobalTheory_TorusCoordPull_O__pull_be9eb376d61b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:13:44.202806+00:00
-- url     : https://prove2.me/theorems/1d3cfde8-1a06-4efa-b285-1525c0094b69
-- title:
--   P2 M Global Theory Torus Coord Pull O  pull be9eb376d61b: P2 M Global Theory Torus Coord Pull O  pull be9eb376d61b
-- statement:
--   The P2 M Global Theory Torus Coord Pull O  pull be9eb376d61b construction uses the P2 M Global Theory Torus Coord Pull O  pull be9eb376d61b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L122-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L122-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusCoordPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
include hp

theorem P2M_GlobalTheory_TorusCoordPull_O__pull_be9eb376d61b (x : D'.X) (κ : Fin 4) :
    D'.Oφ p' x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ D.Oφ p (hD.xe x) κ := by sorry

alias «GlobalTheory».«TorusCoordPull».«Oφ_pull» := P2M_GlobalTheory_TorusCoordPull_O__pull_be9eb376d61b
