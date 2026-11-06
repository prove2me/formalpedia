-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_simplePoleResidue
-- name    : QEC.Coding.AlgebraicGeometry.Differential.exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_simplePoleResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:24.142434+00:00
-- url     : https://prove2.me/theorems/2885daaa-3f8b-4665-bfe6-3eac9fe99994
-- title:
--   Differential: exists polynomial Smith primary Torsion Trace cokernel eq simple Pole Residue
-- statement:
--   Smith bases can be chosen so that the primary trace of an injective
--   polynomial cokernel is the normalized finite-place residue of the resulting
--   diagonal logarithmic differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean#L135-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean#L135-L165

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_simplePoleResidue
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (b : Module.Basis (Fin n) k[X] N)
    (f g : N →ₗ[k[X]] N) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    ∃ source target : Module.Basis (Fin n) k[X] N, ∃ a : Fin n → k[X],
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        GlobalPlace.rationalAdicIdealResidueEquiv p
            (primaryTorsionTrace p.asIdeal
              (cokernelEndomorphism f g hcomm)
                (∑ i, multiplicity p.asIdeal
                  (Ideal.span ({a i} : Set k[X])))) =
          simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
              (LinearMap.toMatrix target target g) a ha) := by sorry
