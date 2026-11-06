-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicSmithLogarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicSmithLogarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:17.734897+00:00
-- url     : https://prove2.me/theorems/941d3630-5b8c-4e96-b0de-61cd5a199b52
-- title:
--   Differential: simple Pole Residue rational Adic Smith Logarithmic Differential
-- statement:
--   The normalized residue of the Smith logarithmic differential is the
--   transported primary trace of the actual Smith cokernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean#L224-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithMatrixResidue.lean#L224-L280

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicSmithLogarithmicDifferential
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha g) =
      GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism f g hcomm) depth) := by sorry
