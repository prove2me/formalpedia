-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_local_reduction_compatibility
-- name    : RandomCNFDeficiency.LowerBound.local_reduction_compatibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:15.209432+00:00
-- url     : https://prove2.me/theorems/1b5858cf-1041-45db-b3d2-cbf9573e3436
-- title:
--   Lemma 3.6 — compatibility of local reductions
-- statement:
--   Let $F$ be a finite CNF on $n$ variables and let real thresholds satisfy $s\ge1$ and $2\le D\le n$. Suppose every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and every $L\subseteq F$ with $s\le|L|\le2s$ satisfies $|N(L)|>D+|L|$. Let $T\subseteq[n]$ with $|T|\le D$. Admissibility, deficiency and closure are the computed notions above.
--
--   Let $K$ be any field, put $A=\operatorname{cl}(T)$, and suppose $A\subseteq B\subseteq F$ with $|B|\le2s$. Every $f\in B_K$ whose variables lie in $T\cup N(A)$ satisfies
--
--   $$R_B(f)=R_A(f).$$
--
--   The letter $B_K$ here denotes the Boolean polynomial algebra, while $B$ alone is the clause set. There is no restriction on the degree of $f$. This equality makes reduction independent of the extra locally satisfiable clauses.
--
--   Differences from the source:
--   - encoding: variables indexed by [n] with Boolean value 1 true → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - encoding: Boolean polynomial quotient with multilinear representatives and fixed degree-lex order → the isomorphic algebra of K-valued Boolean-cube functions, explicit Möbius coefficients, and degree-lex rank with x_(n-1) > ... > x_0; reason: Boolean evaluation identifies exactly the Boolean ideal quotient over every field; the inverse is the multilinear polynomial with these coefficients
--   - generalization: integer s ≥ 1 and degree cutoff D in Theorem 3.1 and its standing context → real s ≥ 1 and real 2 ≤ D ≤ n, comparing all cardinalities and degrees in ℝ; reason: the same maximizer and union bounds use only real inequalities; every integer instance is included and Equation (21) is represented without rounding
--   - encoding: the standing assumptions of Theorem 3.1 and Section 3.1 → Criterion F s D and the displayed variable-set cardinality bounds; reason: Criterion unfolds to all width, local satisfiability, expansion and parameter assumptions, without assuming any closure property
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma 3.6, printed p. 10, PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
import Definitions.Def_RandomCNFDeficiency_LowerBound_ClauseAlgebra
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

theorem local_reduction_compatibility
    {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    {K : Type*} [Field K] (B : CNF n)
    (hAB : closure F s T ⊆ B) (hBF : B ⊆ F) (hB : (B.card : ℝ) ≤ 2 * s)
    (f : BooleanAlgebra n K) (hf : booleanVars f ⊆ T ∪ neighborhood (closure F s T)) :
    localReduction B f = localReduction (closure F s T) f := by sorry

end RandomCNFDeficiency.LowerBound
