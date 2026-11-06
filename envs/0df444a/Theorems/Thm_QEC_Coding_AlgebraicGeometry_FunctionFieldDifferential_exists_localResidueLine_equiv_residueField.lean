-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_exists_localResidueLine_equiv_residueField
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.exists_localResidueLine_equiv_residueField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:01.357782+00:00
-- url     : https://prove2.me/theorems/2b8da2f1-734b-48c6-8236-66015a6341ff
-- title:
--   Function Field Differential: exists local Residue Line equiv residue Field
-- statement:
--   Each local simple-pole quotient is linearly equivalent to the residue
--   field, with existence obtained from an actual principal-cutoff witness.  This
--   is deliberately existential: no witness or residue functional is selected.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1330-L1335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1330-L1335

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.exists_localResidueLine_equiv_residueField (P : GlobalPlace k F) :
    Nonempty (Differential.localResidueLine P ≃ₗ[P.valuationRing]
      GlobalPlace.residueField P) := by sorry
