-- Prove2me | Theorems.Thm_TypeDensity_other_children_count
-- name    : TypeDensity.other_children_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T12:53:26.11503+00:00
-- url     : https://prove2.me/theorems/cac72f16-a643-4651-84cf-39727e033df3
-- title:
--   Counting the "other" children of residue degree `δ` and contact `r` of a unit-weight pattern, their shape, and their total number.
-- statement:
--   This counts the "other" children of residue degree `δ` and contact `r` of a unit-weight pattern, describes their shape, and gives their total number.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L282-L319

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

theorem TypeDensity.other_children_count (n : ℕ) (m : Pattern n) (δ r : ℕ) :
    List.count (δ, State.single 1 r) (otherChildren 1 m) =
        (if h : 1 ≤ δ ∧ δ ≤ n ∧ 1 ≤ r ∧ r ≤ n then
          (m (⟨δ - 1, Nat.sub_one_lt_of_le h.1 h.2.1⟩,
            ⟨r - 1, Nat.sub_one_lt_of_le h.2.2.1 h.2.2.2⟩)).val else 0) ∧
      (∀ z ∈ otherChildren 1 m,
        ∃ ij : Fin n × Fin n, z = (ij.1.val + 1, State.single 1 (ij.2.val + 1))) ∧
      (otherChildren 1 m).length = ∑ ij : Fin n × Fin n, (m ij).val := by sorry
