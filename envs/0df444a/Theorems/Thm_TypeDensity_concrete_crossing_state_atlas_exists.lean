-- Prove2me | Theorems.Thm_TypeDensity_concrete_crossing_state_atlas_exists
-- name    : TypeDensity.concrete_crossing_state_atlas_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:25.264176+00:00
-- url     : https://prove2.me/theorems/7d5b15f5-7d39-41d0-b243-392a0eb0388f
-- title:
--   The crossing state `(a, b, c, h)` of the concrete surface admits an ideal atlas indexed by the crossing residue ideals of the special fiber.
-- statement:
--   The crossing state `(a, b, c, h)` of the concrete surface admits an ideal atlas indexed by the crossing residue ideals of the special fiber.
-- source:
--   TypeDensity/Surfaces/ConcreteAtlas.lean#L39-L87

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
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Theorems.Thm_TypeDensity_special_fiber_crossing_contact_regular
import Theorems.Thm_TypeDensity_crossing_residue_ideal_count
import Theorems.Thm_TypeDensity_concrete_residue_ideal_chart_exists
import Theorems.Thm_TypeDensity_concrete_crossing_state_eq_union_cells
import Theorems.Thm_TypeDensity_crossing_special_fiber_length
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

theorem TypeDensity.concrete_crossing_state_atlas_exists (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hSt : S.t = surfaceT O pi u a b) (hSx : S.x = surfaceX O pi u a b) (hSa : S.a = a)
    (hSb : S.b = b)
    (e : (ConcreteSurface O pi u a b ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      ≃+* SpecialFiber (IsLocalRing.ResidueField O) a b)
    (he : ∀ s : TwoSeries O,
      e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi})
      (surfaceMk O pi u a b s)) = Ideal.Quotient.mk (monomialIdeal (IsLocalRing.ResidueField O) a b)
      (residueSeries O s)) (c h : ℕ) (hc : 0 < c) (hh : 0 < h) :
    ∃ A : IdealAtlas O (ConcreteSurface O pi u a b) pi (a*c+b*h)
      (surfaceStateSet O (ConcreteSurface O pi u a b) S (State.crossing a b c h)),
      Nonempty (A.ι ≃ crossingResidueIdeals (IsLocalRing.ResidueField O) a b c h) := by sorry
