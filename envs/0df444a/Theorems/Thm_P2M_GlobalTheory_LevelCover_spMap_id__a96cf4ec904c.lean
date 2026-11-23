-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LevelCover_spMap_id__a96cf4ec904c
-- name    : P2M_GlobalTheory_LevelCover_spMap_id__a96cf4ec904c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:48.168852+00:00
-- url     : https://prove2.me/theorems/8b5b9870-d467-4baf-bb70-40095523965b
-- title:
--   P2 M Global Theory Level Cover sp Map id  a96cf4ec904c: P2 M Global Theory Level Cover sp Map id  a96cf4ec904c
-- statement:
--   The P2 M Global Theory Level Cover sp Map id  a96cf4ec904c construction uses the P2 M Global Theory Level Cover sp Map id  a96cf4ec904c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean#L65-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
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
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem P2M_GlobalTheory_LevelCover_spMap_id__a96cf4ec904c (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by sorry

alias «GlobalTheory».«LevelCover».«spMap_id'» := P2M_GlobalTheory_LevelCover_spMap_id__a96cf4ec904c
