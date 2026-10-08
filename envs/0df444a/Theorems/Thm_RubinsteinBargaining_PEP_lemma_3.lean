-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_lemma_3
-- name    : RubinsteinBargaining.PEP.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:53:07.353611+00:00
-- url     : https://prove2.me/theorems/b649ed8b-866b-48a0-894e-b47ad113c43f
-- title:
--   Lemma 3 — a preferred delayed offer has a credible response
-- statement:
--   Let $a\in A$. For any partition $b\in[0,1]$ that player 2 strictly prefers in period 1 to $a$ immediately, there is $c\in A$ for which player 1 weakly prefers agreement at $c$ in period 1 to $b$ immediately:
--
--   $$ (b,1)\succ_2(a,0)\quad\Longrightarrow\quad (c,1)\succcurlyeq_1(b,0). $$
--
--   The lemma constrains the continuation available after a rejected counteroffer.
--
--   **Formalization Note** The draft retains the additional (A-4) assumption used for the boundary cases of the preceding lemmas. (A-4) is also needed in the printed Case A itself: from $(b,1)\succ_2(a,0)$ the proof infers $b<a$ by (A-1) and (A-2), which fails at $a=b=1$ (player 2's share zero) unless $(1,0)\succcurlyeq_2(1,1)$, a consequence of (A-4); at $a=b=1$ the conclusion would demand $(c,1)\succcurlyeq_1(1,0)$, which (A-1) and (A-2) rule out.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 104, Lemma 3, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets

namespace RubinsteinBargaining.PEP

theorem lemma_3 (p : Preferences) (h : A1 p ∧ A2 p ∧ A4 p) :
    ∀ a : Partition, a.val ∈ A p →
      ∀ b : Partition,
        strict p .two (agreement b 1) (agreement a 0) →
        ∃ c : Partition, c.val ∈ A p ∧
          weak p .one (agreement c 1) (agreement b 0) := by sorry

end RubinsteinBargaining.PEP
