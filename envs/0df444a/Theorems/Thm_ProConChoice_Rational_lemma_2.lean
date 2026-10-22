-- Prove2me | Theorems.Thm_ProConChoice_Rational_lemma_2
-- name    : ProConChoice.Rational.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:39.362997+00:00
-- url     : https://prove2.me/theorems/2e15f2b9-90a2-4ffd-b2cf-a34937e0704a
-- title:
--   Lemma 2, p. 17 — Möbius inversion over supersets: p(a,S) = Σ_{T⊇S} q(a,T) for all S ∋ a iff (9) for all S ∋ a
-- statement:
--   Let $X$ be a finite set, $a \in X$, and let $p, q$ be any two real-valued functions of an alternative and a subset of $X$. Then the following two families of identities are equivalent:
--   $$p(a, S) = \sum_{S \subseteq T \subseteq X} q(a, T) \quad \text{for every } S \ni a \qquad (8)$$
--   and
--   $$q(a, S) = \sum_{S \subseteq T \subseteq X} (-1)^{|T| - |S|}\, p(a, T) \quad \text{for every } S \ni a. \qquad (9)$$
--
--   This is Möbius inversion on the lattice of supersets of $\{a\}$. It is what makes the transform $q$ of (9) recover $p$ by (8), the identity (24) at the end of Step 1 of the paper's proof.
--
--   **Formalization Note** The equivalence is between the two families for a fixed $a$; for a single set $S$ the two identities are not equivalent. No probability hypothesis is needed, so $p$ and $q$ are arbitrary functions `X → Finset X → ℝ`; the paper's convention $q(a, S) = q(a, S \cup \{a\})$ for $a \notin S$ is not used, since only sets containing $a$ occur.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 17, Lemma 2, eqs. (8) and (9)

import Mathlib

namespace ProConChoice.Rational

/-- Lemma 2 (p. 17): Möbius inversion over supersets. For a fixed alternative `a`, the family of
identities (8) `p(a, S) = ∑_{S ⊆ T ⊆ X} q(a, T)` (all `S ∋ a`) holds iff the family (9)
`q(a, S) = ∑_{S ⊆ T ⊆ X} (-1)^{|T|-|S|} p(a, T)` (all `S ∋ a`) holds. -/
theorem lemma_2 {X : Type*} [Fintype X] [DecidableEq X]
    (p q : X → Finset X → ℝ) (a : X) :
    (∀ S : Finset X, a ∈ S →
        p a S = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T), q a T) ↔
    (∀ S : Finset X, a ∈ S →
        q a S = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T),
          (-1 : ℝ) ^ (T.card - S.card) * p a T) := by sorry

end ProConChoice.Rational
