-- Prove2me | Theorems.Thm_TypeDensity_glued_generators_level_one
-- name    : TypeDensity.glued_generators_level_one
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:45.924566+00:00
-- url     : https://prove2.me/theorems/8cf8bf44-8dec-4f89-9f4d-07d5ccc2b65d
-- title:
--   Level-one generators glued up to a unit can be renormalized to glue exactly.
-- statement:
--   Level-one generators glued up to a unit can be renormalized to glue exactly.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L352-L377

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.glued_generators_level_one (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (gA1 : BlowupChart R t x) (gB1 : BlowupChart R x t)
    (hnorm : ∃ u : Rˣ, (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) gA1 - algebraMap R
    (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x) ^ d * beta.right gB1) ∈
    (Ideal.span {overlapException R t x})) :
    ∃ (FA1 : BlowupChart R t x) (FB1 : BlowupChart R x t), Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R t x)^1) FA1} = Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R t x)^1) gA1} ∧ Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R x t)^1) FB1} = Ideal.span
        {Ideal.Quotient.mk ((chartExceptional R x t)^1) gB1} ∧
        (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) FA1 - (overlapSlope R t x)^d *
        beta.right FB1 ∈ (Ideal.span {overlapException R t x})^1 := by sorry
