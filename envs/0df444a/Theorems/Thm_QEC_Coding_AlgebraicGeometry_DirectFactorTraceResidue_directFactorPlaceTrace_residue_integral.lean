-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorTraceResidue_directFactorPlaceTrace_residue_integral
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorPlaceTrace_residue_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:55.703785+00:00
-- url     : https://prove2.me/theorems/3651406b-7ae2-4662-b31e-1c50154cb55c
-- title:
--   Direct Factor Trace Residue: direct Factor Place Trace residue integral
-- statement:
--   Tracing the actual reduction of an integral element at the packaged place
--   agrees with the canonical ideal-residue-field trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean#L116-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean#L116-L160

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorTraceResidue_constantAlgebra
attribute [local instance] directFactorTraceResidue_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_49
open DirectIntegralDifferentialResidue DirectFactorResidueTransport

theorem QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorPlaceTrace_residue_integral
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorPlaceTrace k F p P
        ((AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b)) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
