-- Prove2me | Theorems.Thm_TypeDensity_residueKillT_apply_ker
-- name    : TypeDensity.residueKillT_apply_ker
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:49.873988+00:00
-- url     : https://prove2.me/theorems/fb8e28e2-d524-4d70-9aa2-d9fa07949aa6
-- title:
--   Values of `residueKillT` on generators;
-- statement:
--   `residueKillT` sends a constant `c` to its residue, `T ↦ 0` and `X ↦ X`; it is surjective with kernel `(π, T)`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L329-L374

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_coeff_substAlgHom_kill
import Theorems.Thm_TypeDensity_mvPowerSeries_mem_span_C_var_iff
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.residueKillT_apply_ker (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (pi : O) (hpi : Irreducible pi) :
    (∀ c : O, residueKillT O (MvPowerSeries.C c) = PowerSeries.C (IsLocalRing.residue O c)) ∧
    residueKillT O (axisT O) = 0 ∧ residueKillT O (axisX O) = PowerSeries.X ∧
    Function.Surjective (residueKillT O) ∧
    RingHom.ker (residueKillT O) = Ideal.span {MvPowerSeries.C pi, axisT O} := by sorry
