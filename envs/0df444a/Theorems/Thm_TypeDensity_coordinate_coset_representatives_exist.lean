-- Prove2me | Theorems.Thm_TypeDensity_coordinate_coset_representatives_exist
-- name    : TypeDensity.coordinate_coset_representatives_exist
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:55.526131+00:00
-- url     : https://prove2.me/theorems/208a5e65-24ae-445b-a129-6d22cc0a601c
-- title:
--   Coordinate vectors over a DVR with finite residue field admit a finite set of unique representatives modulo `π^M`.
-- statement:
--   Coordinate vectors over a DVR with finite residue field admit a finite set of unique representatives modulo `π^M`.
-- source:
--   TypeDensity/Blowup/Charts.lean#L1000-L1037

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Theorems.Thm_TypeDensity_residue_quotient_card
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coordinate_coset_representatives_exist (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (n M : ℕ) :
    ∃ reps : Finset (Fin n → O), ∀ z : Fin n → O, ∃! z₀, z₀ ∈ reps ∧ adicCongr (Ideal.span {pi}) M z
        z₀ := by sorry
