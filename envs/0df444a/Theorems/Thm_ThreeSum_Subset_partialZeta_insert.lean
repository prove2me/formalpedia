-- Prove2me | Theorems.Thm_ThreeSum_Subset_partialZeta_insert
-- name    : ThreeSum.Subset.partialZeta_insert
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:38:43.619021+00:00
-- url     : https://prove2.me/theorems/a68b093f-7901-4612-9f94-8775329f2020
-- title:
--   One-coordinate update of the partial zeta transform
-- statement:
--   Let $\alpha$ be a type with decidable equality, let $f$ assign an integer to each finite subset of $\alpha$, and let $u,P$ be finite subsets. Write $Z_Pf(u)=\sum_{X\subseteq u\cap P}f((u\setminus P)\cup X)$. For a coordinate $a\notin P$,
--
--   $$
--   Z_{P\cup\{a\}}f(u)=\begin{cases}Z_Pf(u)+Z_Pf(u\setminus\{a\})&a\in u,\\Z_Pf(u)&a\notin u.\end{cases}
--   $$
--
--   This is the exact invariant for one ordinary coordinatewise zeta-transform step, with both summands read from the previous stage.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Subset.lean#L300-L346

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Subset.partialZeta_insert : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (u processed : Finset.{u_1} α) (a : α)
  (ha : a ∉ processed),
  @Eq.{1} Int
    (@ThreeSum.Subset.partialZeta.{u_1} α inst
      (@Insert.insert.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instInsert.{u_1} α inst) a processed) f u)
    (@ThreeSum.Subset.zetaStep.{u_1} α inst a (@ThreeSum.Subset.partialZeta.{u_1} α inst processed f) u) := by
  sorry
