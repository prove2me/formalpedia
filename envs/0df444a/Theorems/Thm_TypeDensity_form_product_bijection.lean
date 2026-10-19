-- Prove2me | Theorems.Thm_TypeDensity_form_product_bijection
-- name    : TypeDensity.form_product_bijection
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:55.052385+00:00
-- url     : https://prove2.me/theorems/b8f998a5-3e1e-4977-bedc-b324c12b8f9b
-- title:
--   Over a complete DVR, the normalized form-product map is a bijection from the product of the factor cells onto the product cell.
-- statement:
--   Over a complete DVR, the normalized form-product map is a bijection from the product of the factor cells onto the product cell.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L530-L619

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_form_product_maps_to_and_preserves
import Theorems.Thm_TypeDensity_forms_linear_bijective
import Theorems.Thm_TypeDensity_formProd_add_smul_dvd
import Theorems.Thm_TypeDensity_form_product_congruence_reflects
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

theorem TypeDensity.form_product_bijection (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1) :
    Set.BijOn (reducedFormProduct O d ν g μ)
      (Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
      (reducedFormCell O (∑ i, d i) μ (formProd d g)) := by sorry
