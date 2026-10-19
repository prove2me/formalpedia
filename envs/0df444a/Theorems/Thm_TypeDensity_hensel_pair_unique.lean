-- Prove2me | Theorems.Thm_TypeDensity_hensel_pair_unique
-- name    : TypeDensity.hensel_pair_unique
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:34.895318+00:00
-- url     : https://prove2.me/theorems/dbb2875e-cc1c-4f55-bd3a-3a2aab9df6df
-- title:
--   Uniqueness in Hensel's lemma: monic factorizations with the same coprime residue factors are equal.
-- statement:
--   Uniqueness in Hensel's lemma: monic factorizations with the same coprime residue factors are equal.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L579-L598

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Theorems.Thm_TypeDensity_isCoprime_of_isCoprime_map_residue
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

theorem TypeDensity.hensel_pair_unique (O : Type) [CommRing O] [IsLocalRing O]
    (G H G₁ H₁ : Polynomial O) (hG : G.Monic) (hH : H.Monic) (hG₁ : G₁.Monic) (hH₁ : H₁.Monic)
    (hg : G.map (IsLocalRing.residue O) = G₁.map (IsLocalRing.residue O))
    (hh : H.map (IsLocalRing.residue O) = H₁.map (IsLocalRing.residue O))
    (hc : IsCoprime (G.map (IsLocalRing.residue O)) (H.map (IsLocalRing.residue O)))
    (hp : G * H = G₁ * H₁) :
    G=G₁ ∧ H=H₁ := by sorry
