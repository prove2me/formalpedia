-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_external_hall
-- name    : RandomCNFDeficiency.LowerBound.closure_external_hall
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:34.260485+00:00
-- url     : https://prove2.me/theorems/300d2761-c0aa-4058-8f0f-07f2aacd2576
-- title:
--   Hall inequality outside a deficiency closure
-- statement:
--   Let $F$ be a finite signed CNF on $n$ Boolean variables, with real thresholds $1\le s$ and $2\le D\le n$. Assume every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and $|N(I)|>D+|I|$ whenever $I\subseteq F$ and $s\le |I|\le2s$. Here $N(I)$ is the set of variables occurring in $I$.
--
--   For a protected set $T$ with $|T|\le D$, write $A=\operatorname{cl}_{F,s}(T)$ for its matching-deficiency closure: the union of admissible maximizers of $h_T(I)=|I|-|N(I)\setminus T|$, where admissibility means $I\subseteq F$ and $|I|\le2s$.
--
--   For every $A\subseteq B\subseteq F$ with $|B|\le2s$,
--
--   $$\forall L\subseteq B\setminus A,\qquad |L|\le |N(L)\setminus(T\cup N(A))|.$$
--
--   This is the Hall inequality needed to match remaining clauses to fresh variables while preserving the protected set and the closure.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Lemma 3.5, first displayed inequality, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.closure_external_hall {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) :
    ∀ L ⊆ B \ closure F s T,
      L.card ≤ (neighborhood L \ (T ∪ neighborhood (closure F s T))).card := by sorry
