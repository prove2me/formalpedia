-- Prove2me | Theorems.Thm_ThreeSum_Reporting_frontier_nodup
-- name    : ThreeSum.Reporting.frontier_nodup
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:20.598965+00:00
-- url     : https://prove2.me/theorems/bcbea233-9f9e-49c7-b0d2-11650d91a9d9
-- title:
--   Positive reporting frontiers contain no duplicate prefixes
-- statement:
--   Let $\alpha$ be a type with decidable equality. At each depth $k$, let $C_k$ be a list of possible next symbols, and let $q(k,P)\in\mathbb N$ be a query value for a prefix $P$. Starting with the empty prefix when its query is positive, form each frontier by appending every symbol in $C_k$ to the previous frontier and retaining positive-query prefixes. If every $C_k$ has no duplicates, then
--
--   $$\forall k\in\mathbb N,\qquad\operatorname{Nodup}(F_k).$$
--
--   This structural guarantee holds for arbitrary query values. It ensures that the reporting traversal does not repeat a prefix when each child list is duplicate-free.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Reporting.lean#L105-L124

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_2

theorem ThreeSum.Reporting.frontier_nodup : ∀ {α : Type u_2} [DecidableEq.{u_2 + 1} α] (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat)
  (hc : ∀ (k : Nat), @List.Nodup.{u_2} α (children k)) (k : Nat),
  @List.Nodup.{u_2} (List.{u_2} α) (@ThreeSum.Reporting.frontier.{u_2} α children query k) := by
  sorry
