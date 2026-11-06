-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_primaryTorsionTrace_cokernel_eq_sum
-- name    : QEC.Coding.AlgebraicGeometry.exists_smith_primaryTorsionTrace_cokernel_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:29:20.929247+00:00
-- url     : https://prove2.me/theorems/9159a704-a768-42d0-9ff8-b77b32e05fee
-- title:
--   Algebraic Geometry: exists smith primary Torsion Trace cokernel eq sum
-- statement:
--   Smith bases may be chosen so that the cokernel primary trace of every
--   commuting endomorphism has the diagonal multiplicity formula at the sum of
--   the Smith multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean#L256-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean#L256-L281

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

theorem QEC.Coding.AlgebraicGeometry.exists_smith_primaryTorsionTrace_cokernel_eq_sum
    [IsNoetherianRing R] [Module.Finite R M]
    {n : ℕ} (b : Basis (Fin n) R M)
    (f g : M →ₗ[R] M) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (q : R) (hq : Irreducible q) [hmax : (Ideal.span {q}).IsMaximal] :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        primaryTorsionTrace (Ideal.span {q})
            (cokernelEndomorphism f g hcomm)
              (∑ i, multiplicity q (a i)) =
          ∑ i, (multiplicity q (a i) : R ⧸ Ideal.span {q}) *
            Ideal.Quotient.mk (Ideal.span {q})
              (LinearMap.toMatrix target target g i i) := by sorry
