-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0
-- name    : P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:16.964713+00:00
-- url     : https://prove2.me/theorems/bd5232e8-619c-4ebc-b187-17081636cdaf
-- title:
--   P2 M Global Theory Torus Coord Pull exists good  38f148e1dff0: P2 M Global Theory Torus Coord Pull exists good  38f148e1dff0
-- statement:
--   The P2 M Global Theory Torus Coord Pull exists good  38f148e1dff0 construction uses the P2 M Global Theory Torus Coord Pull exists good  38f148e1dff0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L87-L89

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
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0 (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by sorry

alias «GlobalTheory».«TorusCoordPull».«exists_good'» := P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0
