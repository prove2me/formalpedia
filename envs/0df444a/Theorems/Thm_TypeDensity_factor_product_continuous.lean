-- Prove2me | Theorems.Thm_TypeDensity_factor_product_continuous
-- name    : TypeDensity.factor_product_continuous
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:06.472277+00:00
-- url     : https://prove2.me/theorems/c402fb47-4898-4856-920f-369b94f1b22e
-- title:
--   The factor product map (coefficients of a product of monic polynomials) is continuous and measurable.
-- statement:
--   The factor product map (coefficients of a product of monic polynomials) is continuous and measurable.
-- source:
--   TypeDensity/Unramified/Extension.lean#L503-L521

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.factor_product_continuous (O : Type) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] (ι : Type) [Fintype ι]
    (d : ι → ℕ) :
    Continuous (fun a : (∀ i, Fin (d i) → O) => factorProduct d a) ∧ Measurable
      (fun a : (∀ i, Fin (d i) → O) => factorProduct d a) := by sorry
