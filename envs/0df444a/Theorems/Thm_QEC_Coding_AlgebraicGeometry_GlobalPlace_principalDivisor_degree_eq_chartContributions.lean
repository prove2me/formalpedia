-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_eq_chartContributions
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_eq_chartContributions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:17:53.54396+00:00
-- url     : https://prove2.me/theorems/d9ce1002-04d8-467a-a4a2-f7cb04339e86
-- title:
--   Global Place: principal Divisor degree eq chart Contributions
-- statement:
--   The all-place principal-divisor degree is the sum of the genuine direct
--   affine and finite inverse-fibre contributions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1967-L1982
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1967-L1982

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_eq_chartContributions
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) f) =
      Divisor.degree (AffinePlace.residueDegree k F)
        (AffinePlace.affinePrincipalDivisor k F f) +
      Divisor.degree (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
        (InverseAffinePlace.infinityFibrePrincipalDivisor (k := k) (F := F) f) := by sorry
