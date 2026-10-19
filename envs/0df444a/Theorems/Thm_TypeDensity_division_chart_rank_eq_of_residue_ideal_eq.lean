-- Prove2me | Theorems.Thm_TypeDensity_division_chart_rank_eq_of_residue_ideal_eq
-- name    : TypeDensity.division_chart_rank_eq_of_residue_ideal_eq
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:48.599991+00:00
-- url     : https://prove2.me/theorems/588fd5aa-20f0-49f5-9669-66dc6dedeaeb
-- title:
--   Two division charts whose centres generate the same ideal modulo `π` have the same rank.
-- statement:
--   Two division charts whose centres generate the same ideal modulo `π` have the same rank.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L763-L775

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
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

theorem TypeDensity.division_chart_rank_eq_of_residue_ideal_eq (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [CommRing R] [Algebra O R]
    (pi : O) (hpi : Irreducible pi) (n n' : ℕ) (f g : R) (b : Fin n → R) (c : Fin n' → R)
    (hb : IsDivisionChart O R pi f b) (hc : IsDivisionChart O R pi g c)
    (hres : Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) f} =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap O R pi}) g}) :
    n = n' := by sorry
