-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_deficiency_union_increment
-- name    : RandomCNFDeficiency.LowerBound.deficiency_union_increment
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:29.777442+00:00
-- url     : https://prove2.me/theorems/ebf8bda4-aac2-58a9-948a-46e35a58a374
-- title:
--   Exact increment of matching deficiency for disjoint clause sets
-- statement:
--   Let $A,L$ be disjoint finite families of signed clauses and let $T$ be a set of protected variables. Write $N(I)$ for the variables occurring in a clause family $I$, and define its signed matching deficiency by $h_T(I)=|I|-|N(I)\setminus T|$. Then
--
--   $$h_T(A\cup L)-h_T(A)=|L|-|N(L)\setminus(T\cup N(A))|.$$
--
--   This exact increment identity relates deficiency maximization to Hall expansion on the unprotected variables. It requires no satisfiability or expansion assumption.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Lemma 3.5, first displayed identity, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.deficiency_union_increment {n : ℕ} (T : Finset (Fin n)) (A L : CNF n)
    (h : Disjoint A L) :
    deficiency T (A ∪ L) - deficiency T A =
      (L.card : ℤ) - ((neighborhood L \ (T ∪ neighborhood A)).card : ℤ) := by sorry
