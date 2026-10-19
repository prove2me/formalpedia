-- Prove2me | Theorems.Thm_TypeDensity_factor_product_congruence_iff
-- name    : TypeDensity.factor_product_congruence_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:13.276144+00:00
-- url     : https://prove2.me/theorems/ad806238-3fac-4226-b0ff-cdc90dd47709
-- title:
--   For factor families in the residue cells of pairwise coprime monic `g i`, the factor products are congruent modulo `m^L` iff the families are.
-- statement:
--   For factor families in the residue cells of pairwise coprime monic `g i`, the factor products are congruent modulo `m^L` iff the families are.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L714-L767

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_polynomial_congruence_and_product
import Theorems.Thm_TypeDensity_hensel_family_unique_mod_pow
import Theorems.Thm_TypeDensity_monic_coeff_sub_mem_iff
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

theorem TypeDensity.factor_product_congruence_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O))
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (L : ℕ) (a a' : ∀ i, Fin (g i).natDegree → O)
    (ha : a ∈ Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i)))
    (ha' : a' ∈ Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i))) :
    (∀ j, factorProduct (fun i => (g i).natDegree) a j - factorProduct
        (fun i => (g i).natDegree) a' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔ ∀ i j,
      a i j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L := by sorry
