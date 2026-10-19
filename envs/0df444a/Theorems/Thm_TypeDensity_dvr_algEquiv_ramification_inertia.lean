-- Prove2me | Theorems.Thm_TypeDensity_dvr_algEquiv_ramification_inertia
-- name    : TypeDensity.dvr_algEquiv_ramification_inertia
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:34.695341+00:00
-- url     : https://prove2.me/theorems/369e6c45-e0a9-4d46-be15-626113971a60
-- title:
--   `O`-isomorphic integral DVR extensions of a DVR `O` have the same ramification index and inertia degree.
-- statement:
--   `O`-isomorphic integral DVR extensions of a DVR `O` have the same ramification index and inertia degree.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L42-L68

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_integral_local_extension_unique_prime
import Theorems.Thm_TypeDensity_dvr_extension_maximalIdeal_map_eq_pow
import Theorems.Thm_TypeDensity_dvr_maximalIdeal_pow_injective
import Theorems.Thm_TypeDensity_local_algEquiv_maximalIdeal
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
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.dvr_algEquiv_ramification_inertia (O B B' : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing B']
    [IsDomain B'] [IsDiscreteValuationRing B'] [Algebra O B] [Algebra O B'] [Algebra.IsIntegral O B]
    [Algebra.IsIntegral O B'] (hinj : Function.Injective (algebraMap O B))
    (hinj' : Function.Injective (algebraMap O B')) (φ : B ≃ₐ[O] B') :
    (IsLocalRing.maximalIdeal B).ramificationIdx O = (IsLocalRing.maximalIdeal B').ramificationIdx O
      ∧ (IsLocalRing.maximalIdeal B).inertiaDeg O = (IsLocalRing.maximalIdeal B').inertiaDeg O := by sorry
