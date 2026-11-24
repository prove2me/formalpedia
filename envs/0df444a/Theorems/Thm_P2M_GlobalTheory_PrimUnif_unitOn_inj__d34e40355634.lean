-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PrimUnif_unitOn_inj__d34e40355634
-- name    : P2M_GlobalTheory_PrimUnif_unitOn_inj__d34e40355634
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:57.51871+00:00
-- url     : https://prove2.me/theorems/6109e2a6-a6b2-4a8d-89e8-2dddb8e25a54
-- title:
--   P2 M Global Theory Prim Unif unit On inj  d34e40355634: P2 M Global Theory Prim Unif unit On inj  d34e40355634
-- statement:
--   The P2 M Global Theory Prim Unif unit On inj  d34e40355634 construction uses the P2 M Global Theory Prim Unif unit On inj  d34e40355634 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLatticeUniformisationOfPrimTheta.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLatticeUniformisationOfPrimTheta.lean#L30-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLatticeUniformisationOfPrimTheta
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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PrimUnif

theorem P2M_GlobalTheory_PrimUnif_unitOn_inj__d34e40355634 {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by sorry

alias «GlobalTheory».«PrimUnif».«unitOn_inj'» := P2M_GlobalTheory_PrimUnif_unitOn_inj__d34e40355634
