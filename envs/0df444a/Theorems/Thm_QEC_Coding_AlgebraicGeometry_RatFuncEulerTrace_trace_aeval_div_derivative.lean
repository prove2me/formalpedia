-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncEulerTrace_trace_aeval_div_derivative
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace.trace_aeval_div_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:38.114644+00:00
-- url     : https://prove2.me/theorems/1b2d553a-edb6-422a-9816-8fde43a99249
-- title:
--   Rat Func Euler Trace: trace aeval div derivative
-- statement:
--   Euler's trace identity for the residue of `b / p` at the irreducible
--   polynomial `p`.  The quotient is the actual field `AdjoinRoot p`, and the
--   derivative denominator comes from the trace-dual power basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/EulerTrace.lean#L34-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/EulerTrace.lean#L34-L89

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace
set_option autoImplicit false
open scoped Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace
open Polynomial
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.RatFuncEulerTrace.trace_aeval_div_derivative (p b : k[X])
    [hirr : Fact (Irreducible p)] (hp : p.Monic) (hb : b.degree < p.degree) :
    Algebra.trace k (AdjoinRoot p)
        (Polynomial.aeval (AdjoinRoot.root p) b /
          Polynomial.aeval (AdjoinRoot.root p) p.derivative) =
      b.coeff (p.natDegree - 1) := by sorry
