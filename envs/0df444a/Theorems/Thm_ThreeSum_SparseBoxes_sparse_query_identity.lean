-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity
-- name    : ThreeSum.SparseBoxes.sparse_query_identity
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:26:54.161816+00:00
-- url     : https://prove2.me/theorems/b165edb3-1d16-4a18-a8d6-7a5b27f7104f
-- title:
--   Exact sparse-query decomposition into explicit leaves and boxes
-- statement:
--   Let $q$ be a finite subset of a linearly ordered type, let $t\in\mathbb N$, and let $w$ assign an integer weight to each finite subset. For $u\subseteq q$, define $F(q,u)=\{x\in q\setminus u:\forall y\in u,\ x<y\}$. Let $B(A,F)$ denote the sum of $w(\ell)$ over $A\setminus F\subseteq\ell\subseteq A$. Then
--
--   $$
--   \sum_{\ell\subseteq q}w(\ell)
--   =\sum_{\substack{\ell\subseteq q\\|q\setminus\ell|<t}}w(\ell)
--   +\sum_{\substack{u\subseteq q\\|u|=t}}B(q\setminus u,F(q,u)).
--   $$
--
--   This exact identity separates the near-full subsets into explicit accesses and all remaining subsets into canonical box queries. It holds for signed weights and every threshold, including zero.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SparseBoxes.lean#L518-L542

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.SparseBoxes.sparse_query_identity : ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] (q : Finset.{u_1} α) (t : Nat) (weight : Finset.{u_1} α → Int),
  @Eq.{1} Int (∑ leaf ∈ @Finset.powerset.{u_1} α q, weight leaf)
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
      (∑ leaf ∈ @Finset.powerset.{u_1} α q with
        @LT.lt.{0} Nat instLTNat
          (@Finset.card.{u_1} α
            (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
              (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q leaf))
          t,
        weight leaf)
      (∑ u ∈ @Finset.powersetCard.{u_1} α t q,
        @ThreeSum.SparseBoxes.boxSum.{u_1} α inst
          (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
            (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q u)
          (@ThreeSum.SparseBoxes.queryFree.{u_1} α inst q u) weight)) := by
  sorry
