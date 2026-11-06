-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
-- name    : QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:27:04.041267+00:00
-- url     : https://prove2.me/theorems/98cebc27-f07b-4f61-96e5-1166ff34453e
-- title:
--   Algebraic Geometry: primary Torsion Trace cokernel lmul eq ideal Quotient Mul of eq
-- statement:
--   If `I = (t)`, the equality-indexed principal-cokernel equivalence
--   intertwines induced multiplication by `b` with literal multiplication by
--   `b` on `S / I`, so their finite primary traces agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrincipalCokernelTrace.lean#L110-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrincipalCokernelTrace.lean#L110-L138

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

theorem QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (t b : S) (I : Ideal S)
    (hspan : Ideal.span ({t} : Set S) = I) (depth : ℕ) :
    primaryTorsionTrace p
        (principalCokernelMul (R := R) t b) depth =
      primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)) depth := by sorry
