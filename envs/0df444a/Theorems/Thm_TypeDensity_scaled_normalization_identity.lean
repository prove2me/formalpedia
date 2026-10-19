-- Prove2me | Theorems.Thm_TypeDensity_scaled_normalization_identity
-- name    : TypeDensity.scaled_normalization_identity
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:44.7746+00:00
-- url     : https://prove2.me/theorems/5913336a-11f5-40e1-92ea-ccd06e19076d
-- title:
--   The normalization identity `(1 + π v)(f + π ∑ zᵢ bᵢ) = f + π E⁻¹(s + remainder s)` for a division chart.
-- statement:
--   For a division chart, the normalization identity `(1 + π v)(f + π ∑ zᵢ bᵢ) = f + π E⁻¹(s + remainder s)` holds.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L77-L87

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
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
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.scaled_normalization_identity (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (n : ℕ)
    (pi : O) (f : R) (b : Fin n → R) (E : R ≃ₗ[O] ((Fin n → O) × R))
    (hE : ∀ s, E.symm s = divisionMap f b s) (s : (Fin n → O) × R) :
    (1 + pi • s.2) * (f + pi • coordinateLift b s.1) =
      f + pi • E.symm (adicPerturb (coordinateRemainder pi b E) s) := by sorry
