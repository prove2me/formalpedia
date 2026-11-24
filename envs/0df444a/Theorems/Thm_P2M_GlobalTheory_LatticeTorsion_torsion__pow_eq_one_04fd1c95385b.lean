-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LatticeTorsion_torsion__pow_eq_one_04fd1c95385b
-- name    : P2M_GlobalTheory_LatticeTorsion_torsion__pow_eq_one_04fd1c95385b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:25.586287+00:00
-- url     : https://prove2.me/theorems/652635e6-56eb-411c-ade3-d2d0b2c0ce91
-- title:
--   P2 M Global Theory Lattice Torsion torsion  pow eq one 04fd1c95385b: P2 M Global Theory Lattice Torsion torsion  pow eq one 04fd1c95385b
-- statement:
--   The P2 M Global Theory Lattice Torsion torsion  pow eq one 04fd1c95385b construction uses the P2 M Global Theory Lattice Torsion torsion  pow eq one 04fd1c95385b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteEtaleLatticeTorsionHom.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteEtaleLatticeTorsionHom.lean#L30-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
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
open GlobalTheory GlobalTheory.LatticeTorsion
variable {S : Scheme.{0}}

theorem P2M_GlobalTheory_LatticeTorsion_torsion__pow_eq_one_04fd1c95385b (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by sorry

alias «GlobalTheory».«LatticeTorsion».«torsionι_pow_eq_one» := P2M_GlobalTheory_LatticeTorsion_torsion__pow_eq_one_04fd1c95385b
