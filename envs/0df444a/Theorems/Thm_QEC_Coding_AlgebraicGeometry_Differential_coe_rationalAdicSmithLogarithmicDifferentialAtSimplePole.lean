-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:24.492197+00:00
-- url     : https://prove2.me/theorems/f522ce97-140f-4277-93b7-62e4f9764da4
-- title:
--   Differential: coe rational Adic Smith Logarithmic Differential At Simple Pole
-- statement:
--   The ambient coefficient of the Smith logarithmic differential is the
--   weighted logarithmic derivative of the multiplication matrix in the target
--   basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean#L145-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean#L145-L220

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    ((rationalAdicSmithLogarithmicDifferentialAtSimplePole p
      source target a ha g :
        simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
          Differential k (RatFunc k)) =
      Matrix.trace
          (((algebraMap k[X] (RatFunc k)).mapMatrix
                (LinearMap.toMatrix target target g) *
              (algebraMap k[X] (RatFunc k)).mapMatrix
                (target.toMatrix source)) *
            rationalDiagonalMatrixInverse a *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix
                (LinearMap.toMatrix target target f))) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) := by sorry
