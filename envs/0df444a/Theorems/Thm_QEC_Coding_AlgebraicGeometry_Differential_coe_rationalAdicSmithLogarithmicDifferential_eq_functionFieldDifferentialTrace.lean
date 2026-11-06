-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:46.350193+00:00
-- url     : https://prove2.me/theorems/b9ee7ee0-792e-4ad3-bcf8-e14e0264f04a
-- title:
--   Differential: coe rational Adic Smith Logarithmic Differential eq function Field Differential Trace
-- statement:
--   The ambient Smith logarithmic differential is the actual differential
--   trace of the integral coefficient times the logarithmic differential of the
--   Smith multiplier.  The proof localizes the integral target basis and derives
--   the inverse multiplication matrix from the Smith diagonalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SmithDifferentialTrace.lean#L127-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SmithDifferentialTrace.lean#L127-L257

import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
set_option autoImplicit false
open scoped Polynomial RatFunc nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.smithDifferentialTrace_constantAlgebra
attribute [local instance] smithDifferentialTrace_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.smithDifferentialTrace_scalarTower
attribute [local instance] smithDifferentialTrace_scalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_4de610a81f_51
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_4de610a81f_55
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_4de610a81f_58

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
    {n : ℕ}
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X]
      (_root_.FunctionField.ringOfIntegers k F))
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (t b : _root_.FunctionField.ringOfIntegers k F) (ht : t ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul k[X]
        (_root_.FunctionField.ringOfIntegers k F) t) = Matrix.diagonal a) :
    ((rationalAdicSmithLogarithmicDifferentialAtSimplePole p
        source target a ha
        (Algebra.lmul k[X]
          (_root_.FunctionField.ringOfIntegers k F) b) :
          simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      FunctionFieldDifferential.functionFieldDifferentialTrace
        (k := k) (F := F)
        ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F b) •
          logarithmicDifferential (k := k) (F := F)
            (algebraMap (_root_.FunctionField.ringOfIntegers k F) F t)) := by sorry
