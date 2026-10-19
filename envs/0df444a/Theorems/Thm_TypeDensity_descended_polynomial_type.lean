-- Prove2me | Theorems.Thm_TypeDensity_descended_polynomial_type
-- name    : TypeDensity.descended_polynomial_type
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:14.845849+00:00
-- url     : https://prove2.me/theorems/08b37d48-6b50-47bc-acfe-71bf3f65de03
-- title:
--   Descent of polynomial types: if `F` over `Oδ` has type `σ` with pairwise coprime Frobenius conjugates, and `G ∈ O[X]` maps to the conjugate product of `F`, then `G` has type `scaleType δ σ` over `O`,
-- statement:
--   Descent of polynomial types: if `F` over `Oδ` has type `σ` with pairwise coprime Frobenius conjugates, and `G ∈ O[X]` maps to the conjugate product of `F`, then `G` has type `scaleType δ σ` over `O`, where `δ = deg Φ`.
-- source:
--   TypeDensity/Unramified/DescentTypes.lean#L311-L364

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_frobenius_fraction_extension
import Theorems.Thm_TypeDensity_factor_invariant_unramified_scale
import Theorems.Thm_TypeDensity_invariant_orbit_factors
import Theorems.Thm_TypeDensity_root_field_algEquiv_conjugate_orbit
import Theorems.Thm_TypeDensity_unramified_fraction_field_lift
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open Polynomial

theorem TypeDensity.descended_polynomial_type (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
    (F : Polynomial (AdjoinRoot Φ)) (σ : FactorType)
    (hσ : HasPolynomialTypeF (AdjoinRoot Φ)
      (F.map (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) σ)
    (hcop : ∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime
      ((fun i : Fin Φ.natDegree ↦ (F.map (frobeniusIter O Φ i).toRingHom).map
        (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) i)
      ((fun i : Fin Φ.natDegree ↦ (F.map (frobeniusIter O Φ i).toRingHom).map
        (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) j)) (G : Polynomial O)
    (hG : G.map (algebraMap O (AdjoinRoot Φ)) = conjugateProduct O Φ F) :
    HasPolynomialTypeF O (G.map (algebraMap O (BaseField O))) (scaleType Φ.natDegree σ) := by sorry
