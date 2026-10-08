-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_lemma_1
-- name    : RubinsteinBargaining.PEP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:53:13.155043+00:00
-- url     : https://prove2.me/theorems/3af7c1e2-f891-4f17-a61d-81e288ed003d
-- title:
--   Lemma 1 — a larger demand must be deterred
-- statement:
--   Let $a\in A$, and let $b\in[0,1]$ satisfy $b>a$. Then there is $c\in B$ such that player 2 weakly prefers agreement at $c$ in period 1 to agreement at $b$ immediately:
--
--   $$ (c,1)\succcurlyeq_2(b,0). $$
--
--   This links equilibrium partitions across the two opening orders.
--
--   **Formalization Note** Alongside (A-1) and (A-2), the draft assumes (A-4). The printed proof uses (A-2) to shorten a continuation even when player 2's share is zero, where (A-2) has no force; (A-4) supplies the boundary comparison.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 103, Lemma 1, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets

namespace RubinsteinBargaining.PEP

theorem lemma_1 (p : Preferences) (h : A1 p ∧ A2 p ∧ A4 p) :
    ∀ a : Partition, a.val ∈ A p →
      ∀ b : Partition, a.val < b.val →
        ∃ c : Partition, c.val ∈ B p ∧
          weak p .two (agreement c 1) (agreement b 0) := by sorry

end RubinsteinBargaining.PEP
