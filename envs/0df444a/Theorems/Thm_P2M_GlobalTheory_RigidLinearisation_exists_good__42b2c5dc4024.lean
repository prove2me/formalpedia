-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RigidLinearisation_exists_good__42b2c5dc4024
-- name    : P2M_GlobalTheory_RigidLinearisation_exists_good__42b2c5dc4024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:55.19096+00:00
-- url     : https://prove2.me/theorems/93f01a21-7747-4380-92b4-2fbad3f0b0ef
-- title:
--   P2 M Global Theory Rigid Linearisation exists good  42b2c5dc4024: P2 M Global Theory Rigid Linearisation exists good  42b2c5dc4024
-- statement:
--   The P2 M Global Theory Rigid Linearisation exists good  42b2c5dc4024 construction uses the P2 M Global Theory Rigid Linearisation exists good  42b2c5dc4024 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearisation.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearisation.lean#L37-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearisation
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.RigidLinearisation

theorem P2M_GlobalTheory_RigidLinearisation_exists_good__42b2c5dc4024 {X Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (z : Z) : ∃ J, Good M z J := by sorry

alias «GlobalTheory».«RigidLinearisation».«exists_good'» := P2M_GlobalTheory_RigidLinearisation_exists_good__42b2c5dc4024
