-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_sum
-- name    : QEC.Coding.AlgebraicGeometry.exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:51.684506+00:00
-- url     : https://prove2.me/theorems/54bda596-7357-4f58-a27c-dfb05723a46c
-- title:
--   Algebraic Geometry: exists polynomial Smith primary Torsion Trace cokernel eq sum
-- statement:
--   At a finite rational place, Smith bases identify the primary trace on an
--   injective polynomial cokernel with the diagonal sum weighted by the actual
--   principal-ideal multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean#L308-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean#L308-L339

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
attribute [local instance] QEC.Coding.AlgebraicGeometry.cokernelModuleFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.cyclicQuotientModuleFinite
variable [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_sum
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (b : Basis (Fin n) k[X] N)
    (f g : N →ₗ[k[X]] N) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    ∃ source target : Basis (Fin n) k[X] N, ∃ a : Fin n → k[X],
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        primaryTorsionTrace p.asIdeal
            (cokernelEndomorphism f g hcomm)
              (∑ i, multiplicity p.asIdeal
                (Ideal.span ({a i} : Set k[X]))) =
          ∑ i, (multiplicity p.asIdeal
              (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ p.asIdeal) *
            Ideal.Quotient.mk p.asIdeal
              (LinearMap.toMatrix target target g i i) := by sorry
