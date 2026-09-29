-- Prove2me | Theorems.Thm_Rosenblatt_injective_lift_of_forall_mul_mem_of_forall_mul_ne
-- name    : Rosenblatt.injective_lift_of_forall_mul_mem_of_forall_mul_ne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T16:26:28.543079+00:00
-- url     : https://prove2.me/theorems/817faf7b-3024-4e6b-b389-8a2afa3e8388
-- title:
--   Corollary 2.5: two elements whose translates of a set are disjoint and stay inside it generate a free subsemigroup
-- statement:
--   Let $G$ be a group, let $a, b \in G$, and let $A \subseteq G$ be a **nonempty** subset
--   such that
--
--   * $aA \cup bA \subseteq A$ — for every $x \in A$, both $ax \in A$ and $bx \in A$; and
--   * $aA$ and $bA$ are **disjoint** — for all $x, y \in A$, $ax \neq by$.
--
--   Then $a$ and $b$ generate a free subsemigroup: distinct words in two letters take distinct values
--   when the letters are read as $a$ and $b$.
--
--   *The conclusion, precisely.* Let $W$ be the free monoid on two letters — all finite words,
--   including the empty one, under concatenation — and let $\varphi : W \to G$ send a word
--   $\ell_1 \cdots \ell_k$ to the product of the corresponding elements, multiplied **left to right
--   in the order the letters occur**, with the empty word sent to $1$. Only positive words occur: no
--   letter stands for an inverse and no cancellation is performed. The assertion is that $\varphi$ is
--   injective. Since the empty word is included, this says in particular that no nonempty positive
--   word in $a$ and $b$ equals $1$, and it gives
--   $\exists a, b$ with $\varphi$ injective — the published predicate
--   `Chou.HasFreeSubsemigroupOfRankTwo` — for the group $G$. It does **not** assert anything about
--   inverses, so it is not a statement about a free subgroup.
--
--   *What the hypotheses force.* They are not vacuous, and they are satisfiable: one witness is the
--   group of permutations of $\mathbb{Q}$ with $a : t \mapsto 2t$, $b : t \mapsto 2t + 1$ and $A$ the
--   set of values of nonempty positive words. Two consequences are worth naming because they show
--   the hypotheses are strong. Taking $y = x$ in the disjointness condition forces $a \neq b$. And
--   the two conditions together force $A$, hence $G$, to be **infinite**: a finite $A$ would have to
--   contain the two disjoint sets $aA$ and $bA$, each of the same size as $A$. So every instance with
--   $G$ finite is vacuous.
--
--   The nonemptiness of $A$ is a genuine hypothesis and is not recorded in the declaration's name;
--   without it the disjointness condition holds trivially for any $a, b$ and the conclusion fails.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Corollary 2.5, p. 37, with Proposition 2.4, p. 36

import Mathlib

namespace Rosenblatt

theorem injective_lift_of_forall_mul_mem_of_forall_mul_ne {G : Type*} [Group G] (a b : G)
    (A : Set G) (hA : A.Nonempty)
    (hmem : ∀ x ∈ A, a * x ∈ A ∧ b * x ∈ A)
    (hne : ∀ x ∈ A, ∀ y ∈ A, a * x ≠ b * y) :
    Function.Injective (FreeMonoid.lift ![a, b]) := by
  sorry

end Rosenblatt
