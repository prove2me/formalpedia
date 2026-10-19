-- Prove2me | Theorems.Thm_TypeDensity_image_measurable_of_continuousOn_injOn_compact
-- name    : TypeDensity.image_measurable_of_continuousOn_injOn_compact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:02.549996+00:00
-- url     : https://prove2.me/theorems/2cb01121-d821-4f62-ab17-f04c325daaa3
-- title:
--   The image of a measurable set under a map that is continuous and injective on a closed subset of a compact space (into a Hausdorff space) is measurable.
-- statement:
--   The image of a measurable set under a map that is continuous and injective on a closed subset of a compact space (into a Hausdorff space) is measurable.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L864-L875

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.image_measurable_of_continuousOn_injOn_compact (X Y : Type) [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (f : X → Y) (C : Set X) (hC : IsClosed C)
    (hf : ContinuousOn f C) (hinj : Set.InjOn f C) (U : Set X) (hU : MeasurableSet U) :
    MeasurableSet (f '' (U ∩ C)) := by sorry
