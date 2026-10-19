-- Prove2me | Theorems.Thm_TypeDensity_adic_complete_iff_of_pow_le
-- name    : TypeDensity.adic_complete_iff_of_pow_le
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:15.154666+00:00
-- url     : https://prove2.me/theorems/10988bf8-9efb-4719-8804-51d00108719e
-- title:
--   If `J^k ≤ I ≤ J`, then a module is `I`-adically complete iff it is `J`-adically complete.
-- statement:
--   If `J^k ≤ I ≤ J`, then a module is `I`-adically complete iff it is `J`-adically complete.
-- source:
--   TypeDensity/Unramified/Extension.lean#L251-L279

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

theorem TypeDensity.adic_complete_iff_of_pow_le (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) (k : ℕ) (h1 : J ^ k ≤ I) (h2 : I ≤ J) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by sorry
