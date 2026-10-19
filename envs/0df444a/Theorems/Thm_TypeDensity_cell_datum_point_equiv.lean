-- Prove2me | Theorems.Thm_TypeDensity_cell_datum_point_equiv
-- name    : TypeDensity.cell_datum_point_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:37.068595+00:00
-- url     : https://prove2.me/theorems/01cb04b4-50d6-4aa9-ac20-726a90e60fc5
-- title:
--   Given two-chart curve data matching the divisor of a cell, the children of the cell are in bijection with the points of the curve data, compatibly with the completed local rings, the maps from the sur
-- statement:
--   Given two-chart curve data matching the divisor of a cell, the children of the cell are in bijection with the points of the curve data, compatibly with the completed local rings, the maps from the surface, and the strict transforms.
-- source:
--   TypeDensity/Recursion/Members.lean#L599-L686

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.cell_datum_point_equiv (m : ConcreteMember) (c : m.cellIndex) (D : CellChildData m c)
    (J : Ideal m.R) (beta : BlowupRestriction m.R m.S.t m.S.x)
    (Df : TwoChartCurveData m.R m.S.t m.S.x beta) (hst : (∀ s : Df.ι ⊕ Df.ι0, strictTransformAt m.R
    m.S.t m.S.x (leftPoint Df s) (m.toMeasured.cellDegree c) J = Ideal.span {leftData Df s}) ∧ ∀ s :
    Df.ι ⊕ Df.ιinf, strictTransformAt m.R m.S.x m.S.t (rightPoint Df s) (m.toMeasured.cellDegree c)
    J = Ideal.span {rightData Df s}) (hm : MatchesDivisor D.e Df c.2.1)
    (hpos : (∀ i : Df.ι, 0 < commonMultiplicity Df i) ∧ (∀ k : Df.ι0, 0 < leftMultiplicity Df
    (Sum.inr k)) ∧ ∀ l : Df.ιinf, 0 < rightMultiplicity Df (Sum.inr l)) :
    ∃ ee : m.toMeasured.childIdx c ≃ AllPoints Df, ∀ j : m.toMeasured.childIdx c, ∃ ι :
      divisorLocalRing m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) ≃+* localRing Df (ee j),
      (∀ r : m.R, ι (divisorFromSurface m.R m.S.t m.S.x D.e c.2.1 D.hinf (D.point j) r) =
      localFromSurface Df (ee j) r) ∧ Ideal.map (ι : divisorLocalRing m.R m.S.t m.S.x D.e c.2.1
      D.hinf (D.point j) →+* localRing Df (ee j)) (divisorStrictTransform m.R m.S.t m.S.x D.e c.2.1
      D.hinf (m.toMeasured.cellDegree c) J (D.point j)) = Ideal.span {localCurve Df (ee j)} := by sorry
