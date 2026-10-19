-- Prove2me | Theorems.Thm_TypeDensity_formProd_add_smul_dvd
-- name    : TypeDensity.formProd_add_smul_dvd
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:37.79825+00:00
-- url     : https://prove2.me/theorems/7602556f-447b-4bbf-b74b-a718d334f605
-- title:
--   First-order expansion of a perturbed form product, coefficientwise: `∏ (A i + c H i) ≡ ∏ A i + c ∑ H i ∏_{j ≠ i} A j` modulo `c²`.
-- statement:
--   First-order expansion of a perturbed form product, coefficientwise: `∏ (A i + c H i) ≡ ∏ A i + c ∑ H i ∏_{j ≠ i} A j` modulo `c²`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L251-L264

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_formPoly_add
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
variable {A : Type} [CommRing A] {n : ℕ}
variable {ι : Type} [Fintype ι] {d : ι → ℕ}
open scoped Classical

theorem TypeDensity.formProd_add_smul_dvd (c : A) (A' H : ∀ i, Fin (d i + 1) → A)
    (k : Fin ((∑ i, d i) + 1)) :
    c ^ 2 ∣ formProd d (fun i => A' i + c • H i) k - formProd d A' k -
      c * (∑ i, formPoly (H i) * ∏ j ∈ Finset.univ.erase i, formPoly (A' j)).coeff k := by sorry
