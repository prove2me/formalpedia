-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finsupp_sum_eq_affine_add_infinityFibre
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finsupp_sum_eq_affine_add_infinityFibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:18:03.932209+00:00
-- url     : https://prove2.me/theorems/aa1b456e-ed1d-461c-8804-fcd044fc40aa
-- title:
--   Global Place: finsupp sum eq affine add infinity Fibre
-- statement:
--   A finite-support sum over all normalized global places splits into the
--   direct affine chart and the actual finite inverse-chart fibre over infinity.
--   This exposes only restrictions of the supplied `Finsupp`; the corrected
--   two-chart carrier and its equivalence remain private.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1459-L1501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1459-L1501

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finsupp_sum_eq_affine_add_infinityFibre
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F]
    [AddCommMonoid M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    f.sum (fun _ value => value) =
      (GlobalPlace.affineFinsupp (k := k) (F := F) f).sum
          (fun _ value => value) +
        (GlobalPlace.infinityFibreFinsupp
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (k := k) (F := F) f).sum (fun _ value => value) := by sorry
