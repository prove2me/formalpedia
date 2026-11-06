-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedValuation_eq_of_isEquiv
-- name    : QEC.Coding.AlgebraicGeometry.normalizedValuation_eq_of_isEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:17:41.152331+00:00
-- url     : https://prove2.me/theorems/fa1cb70e-83b0-49bd-92d4-e55d07e5158e
-- title:
--   Algebraic Geometry: normalized Valuation eq of is Equiv
-- statement:
--   Equivalent surjective valuations with the fixed `ℤᵐ⁰` normalization are equal.
--   This is the rigidity bridge from valuation classes to the normalized global-place
--   carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L176-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L176-L182

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry

theorem QEC.Coding.AlgebraicGeometry.normalizedValuation_eq_of_isEquiv
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w := by sorry
