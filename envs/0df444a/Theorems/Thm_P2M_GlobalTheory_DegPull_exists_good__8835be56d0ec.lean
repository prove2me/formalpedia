-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
-- name    : P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:52.504748+00:00
-- url     : https://prove2.me/theorems/d1e36f08-cea2-402b-b6cd-827d391b6781
-- title:
--   P2 M Global Theory Deg Pull exists good  8835be56d0ec: P2 M Global Theory Deg Pull exists good  8835be56d0ec
-- statement:
--   The P2 M Global Theory Deg Pull exists good  8835be56d0ec construction uses the P2 M Global Theory Deg Pull exists good  8835be56d0ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyCubicalPull.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyCubicalPull.lean#L80-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by sorry

alias «GlobalTheory».«DegPull».«exists_good'» := P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
