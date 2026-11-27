-- Prove2me | Theorems.Thm_PeterfalviProblem_InverseClosed_subfield_eq_bot_or_top
-- name    : PeterfalviProblem.InverseClosed.subfield_eq_bot_or_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T04:59:12.732342+00:00
-- url     : https://prove2.me/theorems/0c06df75-4425-4de3-bc0d-77196072005e
-- title:
--   Inverse Closed: subfield eq bot or top
-- statement:
--   A finite field of prime degree over its prime field has no subfield other than the prime
--   field and itself.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/InverseClosedSubgroup.lean#L143-L169
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/InverseClosedSubgroup.lean#L143-L169

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

theorem PeterfalviProblem.InverseClosed.subfield_eq_bot_or_top (hq : q.Prime) (hcard : Fintype.card F = p ^ q) (K : Subfield F) :
    K = ⊥ ∨ K = ⊤ := by sorry
