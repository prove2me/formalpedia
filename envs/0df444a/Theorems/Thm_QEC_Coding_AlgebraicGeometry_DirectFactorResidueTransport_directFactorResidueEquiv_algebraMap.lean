-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:00.107168+00:00
-- url     : https://prove2.me/theorems/d17e7fa1-1720-48c7-9208-cad1a085cdc9
-- title:
--   Direct Factor Residue Transport: direct Factor Residue Equiv algebra Map
-- statement:
--   The direct-factor residue equivalence sends the reduction of an integral
--   element to its actual reduction in the packaged place valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorResidueTransport.lean#L102-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorResidueTransport.lean#L102-L131

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueTransport_constantAlgebra
attribute [local instance] directFactorResidueTransport_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueTransport_isTorsionFree
attribute [local instance] directFactorResidueTransport_isTorsionFree
open DirectIntegralDifferentialResidue

theorem QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorResidueEquiv k F p P
        (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b) =
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
        (directIntegralToValuationRing k F p P b) := by sorry
