-- Prove2me | Theorems.Thm_TypeDensity_hensel_family_unique_mod_pow
-- name    : TypeDensity.hensel_family_unique_mod_pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:39.251039+00:00
-- url     : https://prove2.me/theorems/277531e0-5d0e-4535-aa40-6343e1445b37
-- title:
--   Hensel uniqueness modulo `m^L`: monic factors with pairwise coprime reductions whose products agree modulo `m^L` agree factorwise modulo `m^L`.
-- statement:
--   Hensel uniqueness modulo `m^L`: monic factors with pairwise coprime reductions whose products agree modulo `m^L` agree factorwise modulo `m^L`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L621-L691

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_coprime_family_linear_injective
import Theorems.Thm_TypeDensity_monic_congruent_difference_factor
import Theorems.Thm_TypeDensity_product_first_order_expansion
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.hensel_family_unique_mod_pow (O ι : Type) [CommRing O] [IsLocalRing O] [Fintype ι] (pi : O)
    (hpi : IsLocalRing.maximalIdeal O = Ideal.span {pi}) (hreg : ∀ x : O, pi * x = 0 → x = 0)
    (G G' : ι → Polynomial O) (hG : ∀ i, (G i).Monic) (hG' : ∀ i, (G' i).Monic)
    (hred : ∀ i, (G i).map (IsLocalRing.residue O) = (G' i).map (IsLocalRing.residue O))
    (hc : ∀ i j, i ≠ j → IsCoprime ((G i).map (IsLocalRing.residue O))
      ((G j).map (IsLocalRing.residue O))) (L : ℕ)
    (hp : ∀ j, (∏ i, G i).coeff j - (∏ i, G' i).coeff j ∈ (IsLocalRing.maximalIdeal O) ^ L) :
    ∀ i j, (G i).coeff j - (G' i).coeff j ∈ (IsLocalRing.maximalIdeal O) ^ L := by sorry
