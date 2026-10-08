-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_lemma_2
-- name    : RubinsteinBargaining.PEP.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:53:10.664733+00:00
-- url     : https://prove2.me/theorems/efef9d3e-cec5-4ad7-a2ec-2144d094a48c
-- title:
--   Lemma 2 — a smaller demand must be deterred
-- statement:
--   Let $a\in B$, and let $b\in[0,1]$ satisfy $b<a$. Then there is $c\in A$ such that player 1 weakly prefers agreement at $c$ in period 1 to agreement at $b$ immediately:
--
--   $$ (c,1)\succcurlyeq_1(b,0). $$
--
--   This is the counterpart of Lemma 1 when the players' opening roles are exchanged.
--
--   **Formalization Note** The draft also assumes (A-4), because the printed appeal to (A-2) does not cover a zero share for player 1.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 104, Lemma 2, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets

namespace RubinsteinBargaining.PEP

theorem lemma_2 (p : Preferences) (h : A1 p ∧ A2 p ∧ A4 p) :
    ∀ a : Partition, a.val ∈ B p →
      ∀ b : Partition, b.val < a.val →
        ∃ c : Partition, c.val ∈ A p ∧
          weak p .one (agreement c 1) (agreement b 0) := by sorry

end RubinsteinBargaining.PEP
