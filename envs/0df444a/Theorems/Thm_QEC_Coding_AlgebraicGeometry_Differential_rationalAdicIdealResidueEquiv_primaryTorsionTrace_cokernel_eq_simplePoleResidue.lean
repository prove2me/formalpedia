-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
-- name    : QEC.Coding.AlgebraicGeometry.Differential.rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:01.752181+00:00
-- url     : https://prove2.me/theorems/99bbc833-61c6-4569-ac65-8c57c1578c9c
-- title:
--   Differential: rational Adic Ideal Residue Equiv primary Torsion Trace cokernel eq simple Pole Residue
-- statement:
--   A Smith-diagonal polynomial cokernel has primary trace equal, after the
--   canonical finite-place residue transport, to the normalized residue of its
--   actual diagonal logarithmic differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean#L105-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSmithTraceResidue.lean#L105-L130

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism f g hcomm) depth) =
      simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
          (LinearMap.toMatrix target target g) a ha) := by sorry
