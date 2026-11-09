-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_local_extendability
-- name    : RandomCNFDeficiency.LowerBound.local_extendability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:51.575509+00:00
-- url     : https://prove2.me/theorems/8f1f5bcd-ceb6-4f33-8464-7e6549eeda1a
-- title:
--   Lemma 3.5 — local extendability
-- statement:
--   Let $F$ be a finite CNF on $n$ variables and let real thresholds satisfy $s\ge1$ and $2\le D\le n$. Suppose every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and every $L\subseteq F$ with $s\le|L|\le2s$ satisfies $|N(L)|>D+|L|$. Let $T\subseteq[n]$ with $|T|\le D$. Admissibility, deficiency and closure are the computed notions above.
--
--   Put $A=\operatorname{cl}(T)$, and suppose $A\subseteq B\subseteq F$ with $|B|\le2s$. There exists a partial Boolean assignment $\rho$ such that
--
--   $$\rho\text{ satisfies every }C\in B\setminus A,\qquad
--   \operatorname{dom}(\rho)\cap(T\cup N(A))=\varnothing.$$
--
--   Satisfaction means an actually assigned literal is true, so every extension satisfies the clause. This is an operational extension result independent of the coefficient field.
--
--   Differences from the source:
--   - encoding: variables indexed by [n] with Boolean value 1 true → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: integer s ≥ 1 and degree cutoff D in Theorem 3.1 and its standing context → real s ≥ 1 and real 2 ≤ D ≤ n, comparing all cardinalities and degrees in ℝ; reason: the same maximizer and union bounds use only real inequalities; every integer instance is included and Equation (21) is represented without rounding
--   - encoding: the standing assumptions of Theorem 3.1 and Section 3.1 → Criterion F s D and the displayed variable-set cardinality bounds; reason: Criterion unfolds to all width, local satisfiability, expansion and parameter assumptions, without assuming any closure property
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma 3.5, printed p. 10, PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

theorem local_extendability
    {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D)
    (B : CNF n) (hAB : closure F s T ⊆ B) (hBF : B ⊆ F)
    (hB : (B.card : ℝ) ≤ 2 * s) :
    ∃ ρ : Fin n → Option Bool,
      (∀ C ∈ B \ closure F s T, PartialSatisfies ρ C) ∧
      ∀ i ∈ T ∪ neighborhood (closure F s T), ρ i = none := by sorry

end RandomCNFDeficiency.LowerBound
