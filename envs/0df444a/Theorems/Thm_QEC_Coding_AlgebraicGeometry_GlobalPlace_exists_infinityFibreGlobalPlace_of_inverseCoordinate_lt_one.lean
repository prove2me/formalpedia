-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:17:47.55629+00:00
-- url     : https://prove2.me/theorems/09419700-f736-4397-848d-d64d811e6d89
-- title:
--   Global Place: exists infinity Fibre Global Place of inverse Coordinate lt one
-- statement:
--   A global place where the original inverse coordinate has positive order
--   comes from an actual point of the inverse-chart infinity fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1505-L1538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1505-L1538

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation ((algebraMap (RatFunc k) F RatFunc.X)⁻¹) < 1) :
    ∃ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F,
      P = InverseAffinePlace.infinityFibreGlobalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) D := by sorry
