-- Prove2me | Theorems.Thm_PeterfalviProblem_InverseClosed_pow_four_eq_one_or_forall_mem
-- name    : PeterfalviProblem.InverseClosed.pow_four_eq_one_or_forall_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:02:16.870156+00:00
-- url     : https://prove2.me/theorems/bbea4d23-8f92-5129-8c48-d81c369ccb38
-- title:
--   Inverse Closed: pow four eq one or forall mem
-- statement:
--   Let `F` be a finite field of characteristic three whose degree over `𝔽₃` is prime. Let `W` be
--   an inversion-closed additive subgroup, and let `s ∈ W` be nonzero. Then `W = F` or `s⁴ = 1`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/InverseClosedSubgroup.lean#L173-L205
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/InverseClosedSubgroup.lean#L173-L205

import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_PeterfalviProblem_Algebra_InverseClosedSubgroup
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.InverseClosed
variable {F : Type*} [Field F]
variable (W : AddSubgroup F)
variable [Fintype F] {p q : ℕ} [Fact p.Prime] [CharP F p]

theorem PeterfalviProblem.InverseClosed.pow_four_eq_one_or_forall_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (hp : p = 3) (hq : q.Prime)
    (hcard : Fintype.card F = p ^ q) {s : F} (hs : s ∈ W) (hs0 : s ≠ 0) :
    s ^ 4 = 1 ∨ ∀ x : F, x ∈ W := by sorry
