-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_satisfiable
-- name    : RandomCNFDeficiency.LowerBound.closure_satisfiable
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:41.94842+00:00
-- url     : https://prove2.me/theorems/e4b59966-3ded-474a-a9e8-9f766a52d020
-- title:
--   Every bounded-variable deficiency closure is satisfiable
-- statement:
--   Let $F$ be a finite signed CNF on $n$ Boolean variables, with real thresholds $1\le s$ and $2\le D\le n$. Assume every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and $|N(I)|>D+|I|$ whenever $I\subseteq F$ and $s\le |I|\le2s$. Here $N(I)$ is the set of variables occurring in $I$.
--
--   For a protected set $T$ with $|T|\le D$, write $A=\operatorname{cl}_{F,s}(T)$ for its matching-deficiency closure: the union of admissible maximizers of $h_T(I)=|I|-|N(I)\setminus T|$, where admissibility means $I\subseteq F$ and $|I|\le2s$.
--
--   The closure is satisfiable:
--
--   $$\operatorname{SAT}\bigl(\operatorname{cl}_{F,s}(T)\bigr).$$
--
--   This is the satisfiability property used to make the pseudo-reduction operator preserve the constant polynomial one in Section 3.2.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Section 3.2, Property 1, together with Lemma 3.2, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.closure_satisfiable {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D) : Satisfiable (closure F s T) := by sorry
