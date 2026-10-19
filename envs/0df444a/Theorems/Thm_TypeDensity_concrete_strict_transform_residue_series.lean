-- Prove2me | Theorems.Thm_TypeDensity_concrete_strict_transform_residue_series
-- name    : TypeDensity.concrete_strict_transform_residue_series
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:47.802054+00:00
-- url     : https://prove2.me/theorems/992ff997-810f-4216-9901-34c8c2c6e4f5
-- title:
--   At an exceptional point of the left chart of the concrete surface, the completed local ring is again a concrete surface, and the reduction modulo `T` of a chart element is its residue polynomial shift
-- statement:
--   At an exceptional point of the left chart of the concrete surface, the completed local ring is again a concrete surface, and the reduction modulo `T` of a chart element is its residue polynomial shifted by a root `ᾱ` of the direction polynomial `φ`.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L1074-L1169

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_t_chart_nonrational_point_completion_equiv
import Theorems.Thm_TypeDensity_t_chart_origin_completion_equiv
import Theorems.Thm_TypeDensity_t_chart_unit_point_completion_equiv
import Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
import Theorems.Thm_TypeDensity_twoSeries_ringHom_ext_of_isNilpotent
import Theorems.Thm_TypeDensity_unramified_root_isUnit_of_two_le_natDegree
import Theorems.Thm_TypeDensity_concrete_chart_point_span_form
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_residueKillT_apply_ker
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_unramified_is_dvr
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.concrete_strict_transform_residue_series (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsLocalRing (ConcreteSurface O pi u a b)]
    (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b) ∈ P)
    (e : (((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ⧸ (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ≃+* Polynomial ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b))))
    (he : ∀ r : ConcreteSurface O pi u a b,
      e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
        Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) = Polynomial.X)
    (φ : Polynomial ((IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))) (_hφ : φ.Monic ∧ Irreducible φ)
    (hPφ : (P.map (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))))).map e = Ideal.span {φ}) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (_ : Finite (IsLocalRing.ResidueField O'))
      (pi' : O') (u' : (TwoSeries O')ˣ) (a' b' : ℕ), Irreducible pi' ∧ 0 < a' ∧
    ∃ (Eq : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ≃+* ConcreteSurface O' pi' u' a' b')
      (q : (ConcreteSurface O' pi' u' a' b' ⧸ Ideal.span {surfaceT O' pi' u' a' b'}) ≃+*
        PowerSeries (IsLocalRing.ResidueField O'))
      (ι : (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)) →+* IsLocalRing.ResidueField O')
      (alphaBar : IsLocalRing.ResidueField O'),
      Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b))) =
        surfaceT O' pi' u' a' b' ∧ (φ.map ι).eval alphaBar = 0 ∧
      ∀ FA : (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)), q (Ideal.Quotient.mk (Ideal.span {surfaceT O' pi' u' a' b'})
        (Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P FA))) =
        ((((e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) FA)).map ι).comp
          (Polynomial.X + Polynomial.C alphaBar) : Polynomial (IsLocalRing.ResidueField O')) :
          PowerSeries (IsLocalRing.ResidueField O')) := by sorry
