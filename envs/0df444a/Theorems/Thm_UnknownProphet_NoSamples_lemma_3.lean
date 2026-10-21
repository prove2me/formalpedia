-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_lemma_3
-- name    : UnknownProphet.NoSamples.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:38.432744+00:00
-- url     : https://prove2.me/theorems/8e8cf53e-95ce-4978-a0b2-8b20bb586ea3
-- title:
--   Lemma 3, p. 10 — infinite Ramsey theorem
-- statement:
--   Let $c,d$ be positive integers. Color each $d$-element edge of an infinite complete $d$-uniform hypergraph on vertex set $W$ with one of $c$ colors. Then there is an infinite set of vertices $U\subseteq W$ such that every $d$-element subset of $U$ has the same color:
--
--   $$
--   \exists U\subseteq W,\ |U|=\infty,\ \exists a<c,\ \forall A\subseteq U,\ |A|=d\Longrightarrow\chi(A)=a.
--   $$
--
--   The paper uses this result to find an infinite value set on which a rule's behavior is approximately constant.
--
--   **Formalization Note** The color function is defined on all finite vertex sets; its values outside the $d$-element sets are unused.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 10, Lemma 3

import Mathlib

namespace UnknownProphet.NoSamples

/-- Lemma 3, p. 10: infinite Ramsey for colored uniform hypergraphs. -/
theorem lemma_3 {α : Type*} (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (W : Set α) (hW : W.Infinite) (χ : Finset α → Fin c) :
    ∃ U : Set α, U ⊆ W ∧ U.Infinite ∧
      ∃ col : Fin c, ∀ A : Finset α, (A : Set α) ⊆ U → A.card = d → χ A = col := by sorry

end UnknownProphet.NoSamples
