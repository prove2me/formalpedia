-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_infinityFibrePrincipalDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibrePrincipalDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:17:48.368211+00:00
-- url     : https://prove2.me/theorems/90c932c6-ffe2-4b57-bcd0-e8b3c5e08f87
-- title:
--   Inverse Affine Place: infinity Fibre Principal Divisor apply
-- statement:
--   A coefficient of the inverse-fibre principal divisor is the normalized
--   order of its corresponding inverse-chart global place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1553-L1592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1553-L1592

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibrePrincipalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre k F) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    InverseAffinePlace.infinityFibrePrincipalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (k := k) (F := F) f D =
      GlobalPlace.order (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
        (oldFunctionField := φ) (oldSeparable := σ) k F D) (f : F) := by sorry
