-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_local_satisfiable_extension
-- name    : RandomCNFDeficiency.LowerBound.local_satisfiable_extension
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:34.811054+00:00
-- url     : https://prove2.me/theorems/87a4f883-77a8-5181-a130-c439b67881a5
-- title:
--   Admissible extensions of a deficiency closure remain satisfiable
-- statement:
--   Let $F$ be a finite signed CNF on $n$ Boolean variables, with real thresholds $1\le s$ and $2\le D\le n$. Assume every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and $|N(I)|>D+|I|$ whenever $I\subseteq F$ and $s\le |I|\le2s$. Here $N(I)$ is the set of variables occurring in $I$.
--
--   For a protected set $T$ with $|T|\le D$, write $A=\operatorname{cl}_{F,s}(T)$ for its matching-deficiency closure: the union of admissible maximizers of $h_T(I)=|I|-|N(I)\setminus T|$, where admissibility means $I\subseteq F$ and $|I|\le2s$.
--
--   Every admissible extension of the closure remains satisfiable:
--
--   $$A\subseteq B\subseteq F,\quad |B|\le2s\quad\Longrightarrow\quad\operatorname{SAT}(B).$$
--
--   This corollary expresses the compatibility of local satisfiability with the source's closure-based extension construction.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Corollary of Lemmas 3.2 and 3.5; Section 3.2 Property 1, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.local_satisfiable_extension {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2*s) : Satisfiable B := by sorry
