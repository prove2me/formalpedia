-- Prove2me | Theorems.Thm_TypeDensity_concrete_infinity_strict_transform_multiplicity
-- name    : TypeDensity.concrete_infinity_strict_transform_multiplicity
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:55.985382+00:00
-- url     : https://prove2.me/theorems/fd9482f7-01f4-408f-9ed8-fb7c6c7c144b
-- title:
--   At the point at infinity of the concrete surface, the intersection length of the strict transform of `∑ cᵢ tᵈ⁻ⁱ xⁱ` with the exceptional divisor is `d - deg H`, where `H = ∑ c̄ᵢ Zⁱ` is the residue pol
-- statement:
--   At the point at infinity of the concrete surface, the intersection length of the strict transform of `∑ cᵢ tᵈ⁻ⁱ xⁱ` with the exceptional divisor is `d - deg H`, where `H = ∑ c̄ᵢ Zⁱ` is the residue polynomial.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L1203-L1252

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
import Theorems.Thm_TypeDensity_x_chart_infinity_completion_equiv
import Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
import Theorems.Thm_TypeDensity_concrete_infinity_point_completion
import Theorems.Thm_TypeDensity_residueKillT_xChartSubst
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_residueKillT_apply_ker
import Theorems.Thm_TypeDensity_concrete_surface_equiv_curve_length_and_regular
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
  (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
include hpi ha

theorem TypeDensity.concrete_infinity_strict_transform_multiplicity (d : ℕ) (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)}) [IsLocalRing (ConcreteSurface O pi u a b)]
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) [P.IsMaximal] [P.IsPrime]
    (hx : chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) ∈ P) (hW : chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b) ∈ P) :
    Module.length (CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) P)
      (CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) P ⧸
        Ideal.span {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) P
          (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (c i) * chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b) ^ (d - i.val)),
        completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) P (chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))}) =
    ((d - (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) (c i)) * Polynomial.X^i.val :
      Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b))).natDegree : ℕ) : ℕ∞) := by sorry
