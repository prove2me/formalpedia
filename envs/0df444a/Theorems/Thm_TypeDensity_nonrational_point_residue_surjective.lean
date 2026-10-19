-- Prove2me | Theorems.Thm_TypeDensity_nonrational_point_residue_surjective
-- name    : TypeDensity.nonrational_point_residue_surjective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:13.157759+00:00
-- url     : https://prove2.me/theorems/84fe41a2-9099-4794-a82e-ce5b6b6903ea
-- title:
--   For the chart map `Λ` to the concrete surface over `O[θ] = O[X]/(Φ)` attached to a non-rational point, every element of the target is congruent modulo the parameter ideal to an element in the image of
-- statement:
--   For the chart map `Λ` to the concrete surface over `O[θ] = O[X]/(Φ)` attached to a non-rational point, every element of the target is congruent modulo the parameter ideal to an element in the image of `Λ`.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L48-L111

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_concrete_surface_sub_constantCoeff_mem_parameterIdeal
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.nonrational_point_residue_surjective (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O)
    (hθ : IsUnit (AdjoinRoot.root Φ))
    (Λ : BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) →+* ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)
    (hΛ : ∀ g : TwoSeries O,
      Λ (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      (surfaceMk O pi u a b g)) = surfaceMk (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0
      (chartSubst (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (MvPowerSeries.map (algebraMap O (AdjoinRoot Φ)) g)))
    (hΛZ : Λ (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) =
      surfaceX (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 + algebraMap (AdjoinRoot Φ)
      (ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
      (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
      (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0) (AdjoinRoot.root Φ)) :
    ∀ y : ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
        (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0,
      ∃ x : BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b),
      Λ x - y ∈ surfaceParameterIdeal (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
      (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) * shiftUnit (AdjoinRoot Φ)
        (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 := by sorry
