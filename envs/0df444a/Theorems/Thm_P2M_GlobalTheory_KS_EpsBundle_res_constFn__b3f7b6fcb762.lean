-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_EpsBundle_res_constFn__b3f7b6fcb762
-- name    : P2M_GlobalTheory_KS_EpsBundle_res_constFn__b3f7b6fcb762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:53.045213+00:00
-- url     : https://prove2.me/theorems/b15e2c92-2610-4138-a820-e51bf3c0f873
-- title:
--   P2 M Global Theory KS Eps Bundle res const Fn  b3f7b6fcb762: P2 M Global Theory KS Eps Bundle res const Fn  b3f7b6fcb762
-- statement:
--   The P2 M Global Theory KS Eps Bundle res const Fn  b3f7b6fcb762 construction uses the P2 M Global Theory KS Eps Bundle res const Fn  b3f7b6fcb762 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L15-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TrivialIffCoboundary
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsBundle

theorem P2M_GlobalTheory_KS_EpsBundle_res_constFn__b3f7b6fcb762 {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a := by sorry

alias «GlobalTheory».«KS».«EpsBundle».«res_constFn'» := P2M_GlobalTheory_KS_EpsBundle_res_constFn__b3f7b6fcb762
