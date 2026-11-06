-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_polynomial_eval
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_polynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:02:08.493033+00:00
-- url     : https://prove2.me/theorems/cd1f8997-9007-4ae8-8d6d-e9aa8c9b3ba8
-- title:
--   Meromorphic Germs: nonnegative polynomial eval
-- statement:
--   The coefficient ring and chosen coordinate generate only nonnegative-order polynomials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L108-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L108-L119

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_polynomial_eval
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : R →+* A)
    (hf : ∀ r, 0 ≤ v (f r)) (a : A) (ha : 0 ≤ v a) (p : Polynomial R) :
    0 ≤ v (p.eval₂ f a) := by sorry
