-- Prove2me | Theorems.Thm_TypeDensity_children_degree_identity
-- name    : TypeDensity.children_degree_identity
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:49.213231+00:00
-- url     : https://prove2.me/theorems/0fe271d4-b71b-447a-8c3f-bd6eb41b7875
-- title:
--   Degree identity for one blowup step: for an allowed pattern, `∑ e · deg(child) = deg(s)` over the children `(e, child)`.
-- statement:
--   Degree identity for one blowup step: for an allowed pattern, `∑ e · deg(child) = deg(s)` over the children `(e, child)`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L177-L219

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.children_degree_identity (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) :
    ((children s P).map fun z ↦ z.1 * z.2.degree).sum = s.degree := by sorry
