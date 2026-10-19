-- Prove2me | Theorems.Thm_TypeDensity_isAdicComplete_prod
-- name    : TypeDensity.isAdicComplete_prod
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:42.745635+00:00
-- url     : https://prove2.me/theorems/b9574d38-a693-4729-9ffe-21e61b9fe9e6
-- title:
--   A product of two `I`-adically complete modules is `I`-adically complete.
-- statement:
--   A product of two `I`-adically complete modules is `I`-adically complete.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1044-L1079

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.isAdicComplete_prod (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (I : Ideal O) [IsAdicComplete I M] [IsAdicComplete I N] :
    IsAdicComplete I (M × N) := by sorry
