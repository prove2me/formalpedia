-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:35.777843+00:00
-- url     : https://prove2.me/theorems/1fcf4ec9-fe3c-43e2-8381-0737be04dacc
-- title:
--   Algebraic Geometry: primary Torsion Trace cokernel lmul eq ideal Quotient Mul
-- statement:
--   Under the principal-cokernel equivalence, the primary trace of the
--   endomorphism induced by multiplication by `b` is the primary trace of
--   literal multiplication by `b` on `S / (t)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrincipalCokernelTrace.lean#L143-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrincipalCokernelTrace.lean#L143-L152

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
attribute [local instance] QEC.Coding.AlgebraicGeometry.principalCokernelModuleFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.idealQuotientModuleFinite

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (t b : S) (depth : ℕ) :
    primaryTorsionTrace p
        (principalCokernelMul (R := R) t b) depth =
      primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ Ideal.span ({t} : Set S))
          (Ideal.Quotient.mk (Ideal.span ({t} : Set S)) b)) depth := by sorry
