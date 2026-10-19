-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_curve_basis
-- name    : TypeDensity.concrete_surface_curve_basis
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:52.064492+00:00
-- url     : https://prove2.me/theorems/8bf5c0f2-1ecc-44fa-be60-b3dd6ec00f08
-- title:
--   For `f` regular modulo `π`, a family that is a basis modulo `π` lifts to an `O`-basis of the curve ring `R/(f)`.
-- statement:
--   For `f` regular modulo `π`, a family that is a basis modulo `π` lifts to an `O`-basis of the curve ring `R/(f)`.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L456-L477

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
import Theorems.Thm_TypeDensity_concrete_surface_curve_isAdicComplete
import Theorems.Thm_TypeDensity_dvr_isAdicComplete_span_uniformizer
import Theorems.Thm_TypeDensity_residue_basis_family_basis
import Theorems.Thm_TypeDensity_concrete_surface_pi_regular
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

theorem TypeDensity.concrete_surface_curve_basis (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (f : ConcreteSurface O pi u a b)
    (hf : Function.Injective
      (fun w : ConcreteSurface O pi u a b ⧸ Ideal.span
      {algebraMap O (ConcreteSurface O pi u a b) pi} => Ideal.Quotient.mk
      (Ideal.span {algebraMap O (ConcreteSurface O pi u a b) pi}) f * w)) {N : ℕ}
    (β : Fin N → ConcreteSurface O pi u a b)
    (hβ : ResidueBasisFamily pi (fun i ↦ Ideal.Quotient.mk (Ideal.span {f}) (β i))) :
    ∃ B : Module.Basis (Fin N) O (ConcreteSurface O pi u a b ⧸ Ideal.span {f}), ∀ i,
      B i = Ideal.Quotient.mk (Ideal.span {f}) (β i) := by sorry
