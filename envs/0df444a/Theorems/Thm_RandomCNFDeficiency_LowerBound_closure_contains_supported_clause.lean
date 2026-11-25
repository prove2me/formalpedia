-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_contains_supported_clause
-- name    : RandomCNFDeficiency.LowerBound.closure_contains_supported_clause
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:42.556101+00:00
-- url     : https://prove2.me/theorems/30aa3f33-d4c7-5877-9692-f18c52620b8a
-- title:
--   A clause lies in the closure of any bounded set containing its support
-- statement:
--   Let $F$ be a finite signed CNF on $n$ Boolean variables, with real thresholds $1\le s$ and $2\le D\le n$. Assume every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and $|N(I)|>D+|I|$ whenever $I\subseteq F$ and $s\le |I|\le2s$. Here $N(I)$ is the set of variables occurring in $I$.
--
--   For a protected set $T$ with $|T|\le D$, write $A=\operatorname{cl}_{F,s}(T)$ for its matching-deficiency closure: the union of admissible maximizers of $h_T(I)=|I|-|N(I)\setminus T|$, where admissibility means $I\subseteq F$ and $|I|\le2s$.
--
--   For every clause $C\in F$ whose variables lie in $T$,
--
--   $$\operatorname{Vars}(C)\subseteq T\quad\Longrightarrow\quad C\in\operatorname{cl}_{F,s}(T).$$
--
--   This containment property is used in Section 3.2 to make the pseudo-reduction annihilate each input clause axiom.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Section 3.2, Property 2, the clause-containment argument before Equation (19), printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.closure_contains_supported_clause {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (C : Clause n) (hCF : C ∈ F) (hCT : clauseSupport C ⊆ T) : C ∈ closure F s T := by sorry
