-- Prove2me | Theorems.Thm_TypeDensity_factor_invariant_unramified_scale
-- name    : TypeDensity.factor_invariant_unramified_scale
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:40.863646+00:00
-- url     : https://prove2.me/theorems/92e8be62-2762-4dab-9b9b-78132f8477ed
-- title:
--   For a monic irreducible `H` over `K` whose root field is `K`-isomorphic to the root field of a monic irreducible `g` over `Kδ` (with finite `Oδ`-closure), the factor invariant of `H` is that of `g` wi
-- statement:
--   For a monic irreducible `H` over `K` whose root field is `K`-isomorphic to the root field of a monic irreducible `g` over `Kδ` (with finite `Oδ`-closure), the factor invariant of `H` is that of `g` with inertia degree scaled by `δ = deg Φ`, and `H` has finite `O`-closure.
-- source:
--   TypeDensity/Unramified/DescentTypes.lean#L218-L261

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_closure_finite_descent
import Theorems.Thm_TypeDensity_integral_closure_algEquiv
import Theorems.Thm_TypeDensity_field_invariant_algEquiv
import Theorems.Thm_TypeDensity_field_invariant_unramified_tower
import Theorems.Thm_TypeDensity_unramified_fraction_isSeparable
import Theorems.Thm_TypeDensity_unramified_free_module
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
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
  (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
  (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
    algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c))

theorem TypeDensity.factor_invariant_unramified_scale (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
    (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
      algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c))
    (g : Polynomial (BaseField (AdjoinRoot Φ))) (hg : g.Monic) (hgi : Irreducible g)
    (H : Polynomial (BaseField O)) (hH : H.Monic) (hHi : Irreducible H)
    (hiso : letI := ι.toAlgebra; Nonempty (AdjoinRoot H ≃ₐ[BaseField O] AdjoinRoot g))
    (hfinδ : Module.Finite (AdjoinRoot Φ) (integralClosure (AdjoinRoot Φ) (AdjoinRoot g))) :
    factorInvariant O H = ((factorInvariant (AdjoinRoot Φ) g).1,
      Φ.natDegree * (factorInvariant (AdjoinRoot Φ) g).2) ∧
      Module.Finite O (integralClosure O (AdjoinRoot H)) := by sorry
