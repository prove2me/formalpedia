-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_derivation_extend__1951aa00d8a1
-- name    : P2M_GlobalTheory_T_exists_derivation_extend__1951aa00d8a1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:57.514798+00:00
-- url     : https://prove2.me/theorems/29cc702c-a6e3-4b90-9f67-dadec636bc37
-- title:
--   P2 M Global Theory T exists derivation extend  1951aa00d8a1: P2 M Global Theory T exists derivation extend  1951aa00d8a1
-- statement:
--   The P2 M Global Theory T exists derivation extend  1951aa00d8a1 construction uses the P2 M Global Theory T exists derivation extend  1951aa00d8a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerivationExtendOfFormallySmoothStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerivationExtendOfFormallySmoothStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerivationExtendOfFormallySmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerivationExtendOfFormallySmoothStatement
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
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_derivation_extend__1951aa00d8a1 : ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by sorry

alias «GlobalTheory».«T».«exists_derivation_extend'» := P2M_GlobalTheory_T_exists_derivation_extend__1951aa00d8a1
