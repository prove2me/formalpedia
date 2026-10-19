-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
-- name    : TypeDensity.concrete_surface_quotient_T_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:12.38165+00:00
-- url     : https://prove2.me/theorems/709af8f2-42dd-42c5-97cf-402757c4811b
-- title:
--   The quotient of the concrete surface by `t` is the power series ring `k[[X]]` over the residue field, compatibly with `residueKillT`.
-- statement:
--   The quotient of the concrete surface by `t` is the power series ring `k[[X]]` over the residue field, compatibly with `residueKillT`.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L55-L72

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_residueKillT_apply_ker
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_surface_quotient_T_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) :
    ∃ q : (ConcreteSurface O pi u a b ⧸ Ideal.span {surfaceT O pi u a b}) ≃+*
        PowerSeries (IsLocalRing.ResidueField O),
      ∀ s : TwoSeries O, q (Ideal.Quotient.mk (Ideal.span {surfaceT O pi u a b})
        (surfaceMk O pi u a b s)) = residueKillT O s := by sorry
