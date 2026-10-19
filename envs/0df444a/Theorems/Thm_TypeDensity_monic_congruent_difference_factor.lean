-- Prove2me | Theorems.Thm_TypeDensity_monic_congruent_difference_factor
-- name    : TypeDensity.monic_congruent_difference_factor
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:07.215516+00:00
-- url     : https://prove2.me/theorems/0e3f67d6-f6fe-4b6c-8c5d-b804235ff397
-- title:
--   If monic `G, G'` of degree `n` are congruent modulo `πⁱ` (with `π` a nonzerodivisor), then `G' - G = πⁱ H` with `deg H < n`;
-- statement:
--   If monic `G, G'` of degree `n` are congruent modulo `πⁱ` (with `π` a nonzerodivisor), then `G' - G = πⁱ H` with `deg H < n`; moreover `πⁱ x ∈ (πⁱ⁺¹)` implies `x ∈ (π)`.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L72-L98

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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

theorem TypeDensity.monic_congruent_difference_factor (O : Type) [CommRing O] (pi : O)
    (hreg : ∀ x : O, pi * x = 0 → x = 0) (i n : ℕ) (G G' : Polynomial O) (hG : G.Monic)
    (hG' : G'.Monic) (hn : G.natDegree = n) (hn' : G'.natDegree = n)
    (hcong : ∀ j, G'.coeff j - G.coeff j ∈ Ideal.span {pi ^ i}) :
    (∃ H : Polynomial O, G' - G = Polynomial.C (pi ^ i) * H ∧ H.degree < (n : WithBot ℕ)) ∧
      (∀ x : O, pi ^ i * x ∈ Ideal.span {pi ^ (i + 1)} → x ∈ Ideal.span {pi}) := by sorry
