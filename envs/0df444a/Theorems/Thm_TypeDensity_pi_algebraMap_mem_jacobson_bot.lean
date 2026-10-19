-- Prove2me | Theorems.Thm_TypeDensity_pi_algebraMap_mem_jacobson_bot
-- name    : TypeDensity.pi_algebraMap_mem_jacobson_bot
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:55.754243+00:00
-- url     : https://prove2.me/theorems/a70eaffa-2da6-4c61-8af2-0c11937d53bd
-- title:
--   In a finite product of local `O`-algebras in which `π` is non-invertible, `π` lies in the Jacobson radical, and a componentwise regular element is regular.
-- statement:
--   In a finite product of local `O`-algebras in which `π` is non-invertible, `π` lies in the Jacobson radical, and a componentwise regular element is regular.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L779-L790

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Theorems.Thm_TypeDensity_normalizing_factor_is_unit
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

theorem TypeDensity.pi_algebraMap_mem_jacobson_bot (O : Type) [CommRing O] (ι : Type) (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] [∀ j, IsLocalRing (C j)] (pi : O)
    (hpi : ∀ j, algebraMap O (C j) pi ∈ IsLocalRing.maximalIdeal (C j)) (e : ∀ j, C j)
    (he : ∀ j, Function.Injective (fun z : C j => e j * z)) :
    algebraMap O (∀ j, C j) pi ∈ Ideal.jacobson (⊥ : Ideal (∀ j, C j)) ∧
      Function.Injective (fun z : ∀ j, C j => e * z) := by sorry
