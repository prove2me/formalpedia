-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_VertField_valAt__comp_3a1fda3a8496
-- name    : P2M_GlobalTheory_KS_VertField_valAt__comp_3a1fda3a8496
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:49.600591+00:00
-- url     : https://prove2.me/theorems/0797d25a-3a46-4aca-94c5-fb8bea1e6b65
-- title:
--   P2 M Global Theory KS Vert Field val At  comp 3a1fda3a8496: P2 M Global Theory KS Vert Field val At  comp 3a1fda3a8496
-- statement:
--   The P2 M Global Theory KS Vert Field val At  comp 3a1fda3a8496 construction uses the P2 M Global Theory KS Vert Field val At  comp 3a1fda3a8496 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnVerticalVectorField.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnVerticalVectorField.lean#L50-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorField
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertField

theorem P2M_GlobalTheory_KS_VertField_valAt__comp_3a1fda3a8496 {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by sorry

alias «GlobalTheory».«KS».«VertField».«valAt'_comp» := P2M_GlobalTheory_KS_VertField_valAt__comp_3a1fda3a8496
