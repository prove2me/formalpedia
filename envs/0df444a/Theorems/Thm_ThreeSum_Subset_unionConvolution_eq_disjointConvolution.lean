-- Prove2me | Theorems.Thm_ThreeSum_Subset_unionConvolution_eq_disjointConvolution
-- name    : ThreeSum.Subset.unionConvolution_eq_disjointConvolution
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:48.756164+00:00
-- url     : https://prove2.me/theorems/3317bb84-a1af-44c4-9111-6dbf7dd1f7fc
-- title:
--   Fixed-cardinality union convolution is disjoint convolution
-- statement:
--   Let $\alpha$ have decidable equality and let $f,g$ be integer-valued functions on its finite subsets. Suppose $f(S)\ne0$ implies $|S|=a$ and $g(T)\ne0$ implies $|T|=b$, for fixed $a,b\in\mathbb N$. For a finite set $Q$ with $|Q|=a+b$,
--
--   $$\sum_{\substack{S,T\subseteq Q\\S\cup T=Q}}f(S)g(T)=\sum_{S\subseteq Q}f(S)g(Q\setminus S).$$
--
--   This converts exact-union convolution into the disjoint subset convolution needed by the fixed-cardinality counting construction, even when the coefficients are signed integers.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Subset.lean#L191-L239

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

theorem ThreeSum.Subset.unionConvolution_eq_disjointConvolution : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f g : Finset.{u_1} α → Int) (q : Finset.{u_1} α) (a b : Nat)
  (hf :
    ∀ (s : Finset.{u_1} α),
      @Ne.{1} Int (f s) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α s) a)
  (hg :
    ∀ (v : Finset.{u_1} α),
      @Ne.{1} Int (g v) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α v) b)
  (hq : @Eq.{1} Nat (@Finset.card.{u_1} α q) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)),
  @Eq.{1} Int (@ThreeSum.Subset.unionConvolution.{u_1} α inst f g q)
    (@ThreeSum.Subset.disjointConvolution.{u_1} α inst f g q) := by
  sorry
