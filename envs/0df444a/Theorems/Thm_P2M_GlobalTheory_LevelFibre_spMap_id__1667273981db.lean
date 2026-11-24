-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LevelFibre_spMap_id__1667273981db
-- name    : P2M_GlobalTheory_LevelFibre_spMap_id__1667273981db
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.009036+00:00
-- url     : https://prove2.me/theorems/fbe7bc13-559a-41b1-a8b7-b397f242e723
-- title:
--   P2 M Global Theory Level Fibre sp Map id  1667273981db: P2 M Global Theory Level Fibre sp Map id  1667273981db
-- statement:
--   The P2 M Global Theory Level Fibre sp Map id  1667273981db construction uses the P2 M Global Theory Level Fibre sp Map id  1667273981db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L164-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L164-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {S S' T : Scheme.{0}}

theorem P2M_GlobalTheory_LevelFibre_spMap_id__1667273981db (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by sorry

alias «GlobalTheory».«LevelFibre».«spMap_id'» := P2M_GlobalTheory_LevelFibre_spMap_id__1667273981db
