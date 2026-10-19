-- Prove2me | Theorems.Thm_TypeDensity_concrete_strict_transform_transverse_finite
-- name    : TypeDensity.concrete_strict_transform_transverse_finite
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:08.549517+00:00
-- url     : https://prove2.me/theorems/6467e1df-d273-4377-81e6-dbe45d255097
-- title:
--   At an exceptional point of the blow-up chart, the strict transform `FA` and the exceptional equation `t` are mutually regular in the completed local ring, and some power of the maximal ideal lies in t
-- statement:
--   At an exceptional point of the blow-up chart, the strict transform `FA` and the exceptional equation `t` are mutually regular in the completed local ring, and some power of the maximal ideal lies in the local curve ideal they cut out.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L113-L164

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_exceptional_line_equiv_chart_exceptional
import Theorems.Thm_TypeDensity_blowup_chart_exceptional_point_polynomial
import Theorems.Thm_TypeDensity_concrete_strict_transform_residue_series
import Theorems.Thm_TypeDensity_transverse_of_reduction_ne_zero
import Theorems.Thm_TypeDensity_concrete_left_point_completion_instances
import Theorems.Thm_TypeDensity_concrete_left_point_exceptional_regular
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
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

theorem TypeDensity.concrete_strict_transform_transverse_finite (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (FA : (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) (hne : Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) FA ≠
    0) (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b) ∈ P) : Function.Injective
    (fun w : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ⧸ Ideal.span {completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P FA} =>
    Ideal.Quotient.mk (Ideal.span {completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P FA})
    (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))) * w) ∧ Function.Injective
    (fun w : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ⧸ Ideal.span {completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b))} => Ideal.Quotient.mk
    (Ideal.span {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))})
    (completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P FA) * w) ∧ ∃ L : ℕ,
    ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
    (localCompletionMap (Localization.AtPrime P)))^L ≤ finiteLocalCurveIdeal
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b)) (completedPointMap
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P FA)
    1 := by sorry
