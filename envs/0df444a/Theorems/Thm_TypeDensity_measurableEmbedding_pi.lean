-- Prove2me | Theorems.Thm_TypeDensity_measurableEmbedding_pi
-- name    : TypeDensity.measurableEmbedding_pi
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:23.956783+00:00
-- url     : https://prove2.me/theorems/d0e80406-ba1f-4b3e-aacd-168bc32e2b4e
-- title:
--   A countable product of measurable embeddings is a measurable embedding.
-- statement:
--   A countable product of measurable embeddings is a measurable embedding.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L723-L762

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.measurableEmbedding_pi (ι : Type) [Countable ι] (X Y : ι → Type)
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (Y j)] (f : ∀ j, X j → Y j)
    (hf : ∀ j, MeasurableEmbedding (f j)) :
    MeasurableEmbedding (fun (x : ∀ j, X j) (j : ι) => f j (x j)) := by sorry
