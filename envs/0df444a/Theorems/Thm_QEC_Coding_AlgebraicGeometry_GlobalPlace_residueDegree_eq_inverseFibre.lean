-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_inverseFibre
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_inverseFibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:17:55.124748+00:00
-- url     : https://prove2.me/theorems/95ddfe40-a371-43e9-a872-d9223bbb77f2
-- title:
--   Global Place: residue Degree eq inverse Fibre
-- statement:
--   The canonical all-place residue degree of a global place whose valuation
--   is an inverse-fibre valuation is the residue degree constructed at that
--   inverse-fibre point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1784-L1804
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1784-L1804

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_inverseFibre
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) (D : InverseAffinePlace.infinityFibre k F)
    (hvaluation : @GlobalPlace.valuation k F _ _ _ κ P =
      @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D)) :
    GlobalPlace.residueDegree P =
      InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F) D := by sorry
