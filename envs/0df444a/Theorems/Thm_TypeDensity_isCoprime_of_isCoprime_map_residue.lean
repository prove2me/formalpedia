-- Prove2me | Theorems.Thm_TypeDensity_isCoprime_of_isCoprime_map_residue
-- name    : TypeDensity.isCoprime_of_isCoprime_map_residue
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:05.860797+00:00
-- url     : https://prove2.me/theorems/a0f1d1e4-cfbd-4b8e-b788-a6aaeae3839b
-- title:
--   Monic polynomials over a local ring whose residue reductions are coprime are coprime.
-- statement:
--   Monic polynomials over a local ring whose residue reductions are coprime are coprime.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L569-L577

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

theorem TypeDensity.isCoprime_of_isCoprime_map_residue {O : Type*} [CommRing O] [IsLocalRing O]
    {A B : Polynomial O} (hA : A.Monic) (hB : B.Monic)
    (h : IsCoprime (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))) :
    IsCoprime A B := by sorry
