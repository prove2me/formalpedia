-- Prove2me | Theorems.Thm_TypeDensity_direction_child_member_exists
-- name    : TypeDensity.direction_child_member_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:39:33.92549+00:00
-- url     : https://prove2.me/theorems/18858945-2ce5-4004-9d20-174ab8727b32
-- title:
--   Every support point `Q` of an exceptional divisor (with the boundary contact conditions) carries a child member of degree `deg Q` in the state `pointChildState`, whose ring is identified wit
-- statement:
--   Every support point `Q` of an exceptional divisor (with the boundary contact conditions) carries a child member of degree `deg Q` in the state `pointChildState`, whose ring is identified with the local ring at `Q` compatibly with the exceptional and boundary parameters.
-- source:
--   TypeDensity/Recursion/ChildMembers.lean#L276-L304

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Theorems.Thm_TypeDensity_direction_point_maximal
import Theorems.Thm_TypeDensity_t_chart_point_child_member
import Theorems.Thm_TypeDensity_infinity_point_child_member
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal TensorProduct

theorem TypeDensity.direction_child_member_exists (m : ConcreteMember)
    (e : (BlowupChart m.R m.S.t m.S.x ⧸ chartExceptional m.R m.S.t m.S.x) ≃+* Polynomial
        (IsLocalRing.ResidueField m.R))
    (he : ∀ r : m.R, e (Ideal.Quotient.mk (chartExceptional m.R m.S.t m.S.x)
        (chartBase m.R m.S.t m.S.x r)) = Polynomial.C (IsLocalRing.residue m.R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional m.R m.S.t m.S.x) (chartSlope m.R m.S.t m.S.x)) =
        Polynomial.X)
    (hinf : (infinityPoint m.R m.S.t m.S.x).IsPrime)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField m.R)) (d : ℕ) (Q : divisorSupport Dv)
    (hb : Q.val = infinityDirection (IsLocalRing.ResidueField m.R) → d < stateContactT m.s)
    (hz : Q.val = zeroDirection (IsLocalRing.ResidueField m.R) →
      ∀ h : ℕ, stateContactX m.s = some h → d < h) :
    ∃ cm : ChildMember m (directionDegree (IsLocalRing.ResidueField m.R) Q.val)
        (pointChildState (IsLocalRing.ResidueField m.R) m.s d Dv Q.val),
    ∃ Eq : divisorLocalRing m.R m.S.t m.S.x e Dv hinf Q ≃+* cm.mc.R,
    Eq (divisorException m.R m.S.t m.S.x e Dv hinf Q) = cm.mc.S.t ∧
    ((Q.val = infinityDirection (IsLocalRing.ResidueField m.R) ∨ Q.val = zeroDirection
        (IsLocalRing.ResidueField m.R)) → Eq (divisorBoundary m.R m.S.t m.S.x e Dv hinf Q) =
        cm.mc.S.x) ∧
    ∀ r : m.O,
    Eq (divisorFromSurface m.R m.S.t m.S.x e Dv hinf Q (algebraMap m.O m.R r)) = algebraMap cm.mc.O
        cm.mc.R (algebraMap m.O cm.mc.O r) := by sorry
