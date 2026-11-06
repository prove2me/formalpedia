-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_repackage
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_repackage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:19:03.624191+00:00
-- url     : https://prove2.me/theorems/8d8b48d9-de2c-4e3d-b4d7-6e8063b873ad
-- title:
--   Global Place: residue Degree repackage
-- statement:
--   Repackaging a global place for another constant-field algebra preserves
--   the residue degree transported from the complete two-chart decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1619-L1670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean#L1619-L1670

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_repackage
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (oldAlgebra newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace.residueDegree k F _ _ _ π ρ τ φ σ newAlgebra
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
      @GlobalPlace.residueDegree k F _ _ _ π ρ τ φ σ oldAlgebra P := by sorry
