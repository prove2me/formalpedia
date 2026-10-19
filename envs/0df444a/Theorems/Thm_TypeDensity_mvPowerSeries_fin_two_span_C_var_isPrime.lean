-- Prove2me | Theorems.Thm_TypeDensity_mvPowerSeries_fin_two_span_C_var_isPrime
-- name    : TypeDensity.mvPowerSeries_fin_two_span_C_var_isPrime
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:51.244096+00:00
-- url     : https://prove2.me/theorems/f4f52993-f52a-47d8-998c-a86322ad6ff3
-- title:
--   If `(c)` is prime in `A`, then `(c, X s)` is prime in `A[[X 0, X 1]]`: it is the kernel of killing `X s` and reducing the coefficients modulo `c`, with values in the domain `(A/(c))[[Y]]`.
-- statement:
--   If `(c)` is prime in `A`, then `(c, X s)` is prime in `A[[X 0, X 1]]`: it is the kernel of killing `X s` and reducing the coefficients modulo `c`, with values in the domain `(A/(c))[[Y]]`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L563-L584

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_coeff_substAlgHom_kill
import Theorems.Thm_TypeDensity_mvPowerSeries_mem_span_C_var_iff
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

theorem TypeDensity.mvPowerSeries_fin_two_span_C_var_isPrime (A : Type) [CommRing A] (c : A)
    (hc : (Ideal.span {c}).IsPrime) (s : Fin 2) :
    (Ideal.span {(MvPowerSeries.C c : MvPowerSeries (Fin 2) A), MvPowerSeries.X s}).IsPrime := by sorry
