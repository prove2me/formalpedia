-- Prove2me | Theorems.Thm_TypeDensity_form_product_congruence_reflects
-- name    : TypeDensity.form_product_congruence_reflects
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:31.795997+00:00
-- url     : https://prove2.me/theorems/0ffda2e7-8713-4c65-9396-49c1abfc2129
-- title:
--   The normalized form-product map reflects congruences: if the products of two families in the factor cells agree modulo `m^L`, so do the families.
-- statement:
--   The normalized form-product map reflects congruences: if the products of two families in the factor cells agree modulo `m^L`, so do the families.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L357-L410

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_form_product_maps_to_and_preserves
import Theorems.Thm_TypeDensity_forms_linear_injective
import Theorems.Thm_TypeDensity_formProd_add_smul_dvd
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

theorem TypeDensity.form_product_congruence_reflects (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : Type) [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O) (hgν : ∀ i, g i (ν i) = 1)
    (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1)) (hμ : formProd d g μ = 1)
    (a a' : ∀ i, Fin (d i) → O)
    (ha : a ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
    (ha' : a' ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))) (L : ℕ)
    (hL : ∀ j, reducedFormProduct O d ν g μ a j - reducedFormProduct O d ν g μ a' j ∈
      (IsLocalRing.maximalIdeal O) ^ L) :
    ∀ i j, a i j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L := by sorry
