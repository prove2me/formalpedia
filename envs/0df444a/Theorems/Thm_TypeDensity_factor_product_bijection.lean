-- Prove2me | Theorems.Thm_TypeDensity_factor_product_bijection
-- name    : TypeDensity.factor_product_bijection
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:01.299064+00:00
-- url     : https://prove2.me/theorems/27a241a2-be7d-4777-a031-4394234bd26a
-- title:
--   Over a complete local ring, multiplying monic lifts gives a bijection from the product of the residue cells of pairwise coprime monic `gᵢ` onto the residue cell of `∏ gᵢ` (Hensel).
-- statement:
--   Over a complete local ring, multiplying monic lifts gives a bijection from the product of the residue cells of pairwise coprime monic `gᵢ` onto the residue cell of `∏ gᵢ` (Hensel).
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L126-L175

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_hensel_family_exists
import Theorems.Thm_TypeDensity_hensel_family_unique
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
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

theorem TypeDensity.factor_product_bijection (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) :
    Set.BijOn (factorProduct (fun i ↦ (g i).natDegree))
      (Set.pi Set.univ (fun i ↦ residueCell O (g i).natDegree (g i)))
      (residueCell O (∑ i, (g i).natDegree) (∏ i, g i)) := by sorry
