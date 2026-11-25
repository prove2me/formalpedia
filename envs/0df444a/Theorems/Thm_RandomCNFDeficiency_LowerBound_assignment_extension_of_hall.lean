-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_assignment_extension_of_hall
-- name    : RandomCNFDeficiency.LowerBound.assignment_extension_of_hall
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T20:12:16.78702+00:00
-- url     : https://prove2.me/theorems/c654c13a-0fae-44e5-88ad-67d4bfbcb224
-- title:
--   Hall expansion outside protected variables extends any prescribed assignment
-- statement:
--   Let $H$ be a finite signed CNF and $S$ a protected variable set. Assume $|L|\le |N(L)\setminus S|$ for every subfamily $L\subseteq H$. For every initial total Boolean assignment $a$, there is a total assignment $b$ such that
--
--   $$b|_S=a|_S,\qquad b\models H.$$
--
--   Thus arbitrary prescribed values on the protected set are compatible with satisfying all clauses. This records the assignment-preserving consequence of the Hall-based local extendability construction.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Lemma 3.5, printed p. 10 / PDF p. 12, Hall matching and consistent assignment construction; assignment-preserving corollary. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Clause
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.assignment_extension_of_hall {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (hH : ∀ L ⊆ H, L.card ≤ (neighborhood L \ S).card) (a : Assignment n) :
    ∃ b : Assignment n, (∀ i ∈ S, b i=a i) ∧ ∀ C ∈ H, SatisfiesClause b C := by sorry
