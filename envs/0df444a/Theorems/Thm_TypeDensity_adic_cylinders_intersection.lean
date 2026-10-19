-- Prove2me | Theorems.Thm_TypeDensity_adic_cylinders_intersection
-- name    : TypeDensity.adic_cylinders_intersection
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:03.667184+00:00
-- url     : https://prove2.me/theorems/0e827c7f-d9c3-4803-9d3a-9c70fe29be32
-- title:
--   Adic cylinders form a π-system.
-- statement:
--   Adic cylinders form a π-system.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L57-L81

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.adic_cylinders_intersection (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    IsPiSystem (adicCylinders I M) := by sorry
