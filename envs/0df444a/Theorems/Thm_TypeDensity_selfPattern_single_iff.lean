-- Prove2me | Theorems.Thm_TypeDensity_selfPattern_single_iff
-- name    : TypeDensity.selfPattern_single_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:08.723152+00:00
-- url     : https://prove2.me/theorems/467edc2e-274f-4016-b25b-753926764edd
-- title:
--   An allowed tangent pattern of `S(a;n)` (`n ≥ 2`) is the self pattern exactly when `d = n`, there is no tangent part, and the off-boundary pattern is the single point of type `(1, n-1)`.
-- statement:
--   An allowed tangent pattern of `S(a;n)` (`n ≥ 2`) is the self pattern exactly when `d = n`, there is no tangent part, and the off-boundary pattern is the single point of type `(1, n-1)`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L548-L588

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.selfPattern_single_iff (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n)
    (P : TangentPattern (State.single a n).degree) (hP : Allowed (State.single a n) P) :
    SelfPattern (State.single a n) P ↔ (P.d.val = n ∧ P.rt.val = 0 ∧ P.rx.val = 0 ∧
        ∀ ij : Fin (State.single a n).degree × Fin (State.single a n).degree, (P.other ij).val =
        (if ij.1.val = 0 ∧ ij.2.val = n - 1 then 1 else 0)) := by sorry
