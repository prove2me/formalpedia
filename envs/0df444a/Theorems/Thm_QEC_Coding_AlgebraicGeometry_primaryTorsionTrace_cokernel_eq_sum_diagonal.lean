-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_eq_sum_diagonal
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_eq_sum_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:53.80534+00:00
-- url     : https://prove2.me/theorems/9e933775-4f1d-4790-b933-acf032fb78d9
-- title:
--   Algebraic Geometry: primary Torsion Trace cokernel eq sum diagonal
-- statement:
--   For a Smith-diagonal presentation of an injective endomorphism, the
--   primary trace of a commuting endomorphism on its cokernel is the sum of the
--   diagonal target-basis coefficients weighted by the corresponding
--   multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean#L209-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/SmithTrace.lean#L209-L251

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

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_eq_sum_diagonal
    [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    (source target : Basis (Fin n) R M)
    (a : Fin n → R) (ha : ∀ i, a i ≠ 0)
    (f g : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (q : R) (hq : Irreducible q) [hmax : (Ideal.span {q}).IsMaximal]
    (depth : ℕ) (hdepth : ∀ i, multiplicity q (a i) ≤ depth) :
    primaryTorsionTrace (Ideal.span {q})
        (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity q (a i) : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q})
          (LinearMap.toMatrix target target g i i) := by sorry
