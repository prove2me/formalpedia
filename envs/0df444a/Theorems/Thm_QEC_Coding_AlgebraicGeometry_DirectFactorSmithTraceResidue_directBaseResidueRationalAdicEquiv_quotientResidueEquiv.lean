-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:31.558592+00:00
-- url     : https://prove2.me/theorems/5bf8e98c-46c7-404d-913b-c969defad51f
-- title:
--   Direct Factor Smith Trace Residue: direct Base Residue Rational Adic Equiv quotient Residue Equiv
-- statement:
--   The canonical base-residue transport agrees on the common quotient
--   representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSmithTraceResidue.lean#L70-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSmithTraceResidue.lean#L70-L77

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSmithTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_49
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue._p2m_local_instance_176fcc4610_53
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
open DirectFactorSemilocalLogarithmicResidue

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (x : R k ⧸ p.asIdeal) :
    directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.quotientResidueEquiv p.asIdeal x) =
      GlobalPlace.rationalAdicIdealResidueEquiv p x := by sorry
