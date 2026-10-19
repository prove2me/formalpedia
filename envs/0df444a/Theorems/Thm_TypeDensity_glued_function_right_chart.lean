-- Prove2me | Theorems.Thm_TypeDensity_glued_function_right_chart
-- name    : TypeDensity.glued_function_right_chart
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:20.526124+00:00
-- url     : https://prove2.me/theorems/dddbe0c2-7579-46ea-a1ef-5eedaee6325f
-- title:
--   A surface function lifting the glued pair agrees with it on the `x`-chart modulo `(x)^j`.
-- statement:
--   A surface function lifting the glued pair agrees with it on the `x`-chart modulo `(x)^j`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L296-L305

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

theorem TypeDensity.glued_function_right_chart (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d) (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ
    (gluedFunctionPair R t x G j)) (j : ℕ) :
    algebraMap R (BlowupChart R x t) f - (chartBase R x t x)^d * G.right j ∈
        (chartExceptional R x t)^j := by sorry
