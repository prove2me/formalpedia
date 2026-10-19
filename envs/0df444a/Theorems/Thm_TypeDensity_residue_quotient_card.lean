-- Prove2me | Theorems.Thm_TypeDensity_residue_quotient_card
-- name    : TypeDensity.residue_quotient_card
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:01.546988+00:00
-- url     : https://prove2.me/theorems/b2ba22bc-b87f-40a2-ace3-a74019524a12
-- title:
--   In a DVR with finite residue field, `#(O/𝔪^L) = q ^ L`.
-- statement:
--   In a DVR with finite residue field, `#(O/𝔪^L) = q ^ L`.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L1158-L1164

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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

theorem TypeDensity.residue_quotient_card (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (L : ℕ) :
    Nat.card (O ⧸ (IsLocalRing.maximalIdeal O)^L)=(Nat.card (IsLocalRing.ResidueField O))^L := by sorry
