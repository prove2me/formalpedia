-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LinearMap_trace_eq_restrict_add_quotient
-- name    : QEC.Coding.AlgebraicGeometry.LinearMap.trace_eq_restrict_add_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:58.561002+00:00
-- url     : https://prove2.me/theorems/49e70355-a1f5-4832-a7d1-9c1f790b2a3b
-- title:
--   Linear Map: trace eq restrict add quotient
-- statement:
--   Trace is additive across an invariant subspace and the induced quotient
--   endomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/LinearTraceInvariantQuotient.lean#L28-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/LinearTraceInvariantQuotient.lean#L28-L82

import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_LinearTraceInvariantQuotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.LinearMap
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem QEC.Coding.AlgebraicGeometry.LinearMap.trace_eq_restrict_add_quotient (f : V →ₗ[K] V) (p : Submodule K V)
    (hf : p ≤ p.comap f) :
    LinearMap.trace K V f =
      LinearMap.trace K p
          ((f.domRestrict p).codRestrict p (fun x => hf x.property)) +
        LinearMap.trace K (V ⧸ p) (p.mapQ p f hf) := by sorry
