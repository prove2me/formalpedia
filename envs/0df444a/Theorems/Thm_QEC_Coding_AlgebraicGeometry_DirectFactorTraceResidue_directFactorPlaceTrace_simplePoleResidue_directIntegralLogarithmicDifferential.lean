-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorTraceResidue_directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:02.588438+00:00
-- url     : https://prove2.me/theorems/8e5f0dbd-942b-436c-9663-00df5725e6e7
-- title:
--   Direct Factor Trace Residue: direct Factor Place Trace simple Pole Residue direct Integral Logarithmic Differential
-- statement:
--   The base-residue-field trace of the normalized local residue of an
--   integral multiple of the base logarithmic differential is the upper residue
--   trace weighted by the genuine ramification index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean#L165-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean#L165-L189

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

theorem QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorPlaceTrace k F p P
        (Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (directIntegralLogarithmicDifferentialAtSimplePole k F p P b)) =
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          p.asIdeal.ResidueField) *
        Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
