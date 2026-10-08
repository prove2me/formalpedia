-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_lemma_4
-- name    : RubinsteinBargaining.PEP.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:53:21.877491+00:00
-- url     : https://prove2.me/theorems/3cd2d44e-a893-4e0d-b754-e26c1d1c5897
-- title:
--   Lemma 4 — the symmetric credible response
-- statement:
--   Let $a\in B$. For any partition $b\in[0,1]$ that player 1 strictly prefers in period 1 to $a$ immediately, there is $c\in B$ for which player 2 weakly prefers agreement at $c$ in period 1 to $b$ immediately:
--
--   $$ (b,1)\succ_1(a,0)\quad\Longrightarrow\quad (c,1)\succcurlyeq_2(b,0). $$
--
--   This is the role-exchanged counterpart of Lemma 3.
--
--   **Formalization Note** The draft retains (A-4) for the same zero-share boundary issue.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 104, Lemma 4, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets

namespace RubinsteinBargaining.PEP

theorem lemma_4 (p : Preferences) (h : A1 p ∧ A2 p ∧ A4 p) :
    ∀ a : Partition, a.val ∈ B p →
      ∀ b : Partition,
        strict p .one (agreement b 1) (agreement a 0) →
        ∃ c : Partition, c.val ∈ B p ∧
          weak p .two (agreement c 1) (agreement b 0) := by sorry

end RubinsteinBargaining.PEP
