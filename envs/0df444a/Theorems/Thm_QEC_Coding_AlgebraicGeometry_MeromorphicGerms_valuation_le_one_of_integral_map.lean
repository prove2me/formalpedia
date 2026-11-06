-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_valuation_le_one_of_integral_map
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.valuation_le_one_of_integral_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:58.941288+00:00
-- url     : https://prove2.me/theorems/34d9e257-7fae-4e20-af4a-455fcb982050
-- title:
--   Meromorphic Germs: valuation le one of integral map
-- statement:
--   Integral elements over coefficients in a valuation ring have no pole.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L90-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L90-L97

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

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.valuation_le_one_of_integral_map
    {R A Γ : Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation A Γ) (f : R →+* A) (hf : ∀ r, v (f r) ≤ 1)
    {a : A} (ha : f.IsIntegralElem a) : v a ≤ 1 := by sorry
