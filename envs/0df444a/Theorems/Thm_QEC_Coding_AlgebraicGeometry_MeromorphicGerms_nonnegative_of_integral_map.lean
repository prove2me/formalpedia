-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_of_integral_map
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_of_integral_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:01:47.97475+00:00
-- url     : https://prove2.me/theorems/46e23671-3ec4-46c0-9956-1af979132ace
-- title:
--   Meromorphic Germs: nonnegative of integral map
-- statement:
--   Nonnegative additive valuation rings contain every integral element over them.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L100-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L100-L105

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

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegative_of_integral_map
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : R →+* A)
    (hf : ∀ r, 0 ≤ v (f r)) {a : A} (ha : f.IsIntegralElem a) :
    0 ≤ v a := by sorry
