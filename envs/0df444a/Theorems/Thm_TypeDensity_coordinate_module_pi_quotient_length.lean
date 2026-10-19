-- Prove2me | Theorems.Thm_TypeDensity_coordinate_module_pi_quotient_length
-- name    : TypeDensity.coordinate_module_pi_quotient_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:55.546171+00:00
-- url     : https://prove2.me/theorems/30e8106d-80f2-4555-826c-333dad60fd77
-- title:
--   For a free module `V ≅ O^n` over a DVR with uniformizer `π`, multiplication by `π` is injective and `V / πV` has length `n`.
-- statement:
--   For a free module `V ≅ O^n` over a DVR with uniformizer `π`, multiplication by `π` is injective and `V / πV` has length `n`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L619-L659

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.coordinate_module_pi_quotient_length (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (n : ℕ) (V : Type) [AddCommGroup V] [Module O V]
    (EV : V ≃ₗ[O] (Fin n → O)) :
    Function.Injective (fun v : V => pi • v) ∧
      Module.length O (V ⧸ LinearMap.range (pi • (LinearMap.id : V →ₗ[O] V))) = (n : ℕ∞) := by sorry
