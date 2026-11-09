-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_closure_largest_maximizer
-- name    : RandomCNFDeficiency.LowerBound.closure_largest_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:21.623597+00:00
-- url     : https://prove2.me/theorems/0bd1b252-2a5a-48c7-8911-ff3cb5f010f4
-- title:
--   Lemma 3.2 — largest deficiency maximizer
-- statement:
--   Let $F$ be a finite CNF on $n$ variables and let real thresholds satisfy $s\ge1$ and $2\le D\le n$. Suppose every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and every $L\subseteq F$ with $s\le|L|\le2s$ satisfies $|N(L)|>D+|L|$. Let $T\subseteq[n]$ with $|T|\le D$. Admissibility, deficiency and closure are the computed notions above.
--
--   There is a unique inclusion-wise largest admissible maximizer of deficiency, it equals the defined closure, and
--
--   $$|\operatorname{cl}(T)|<s.$$
--
--   This theorem establishes the validity of the union-of-maximizers definition and its strict size bound.
--
--   Differences from the source:
--   - encoding: variables indexed by [n] with Boolean value 1 true → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: integer s ≥ 1 and degree cutoff D in Theorem 3.1 and its standing context → real s ≥ 1 and real 2 ≤ D ≤ n, comparing all cardinalities and degrees in ℝ; reason: the same maximizer and union bounds use only real inequalities; every integer instance is included and Equation (21) is represented without rounding
--   - encoding: the standing assumptions of Theorem 3.1 and Section 3.1 → Criterion F s D and the displayed variable-set cardinality bounds; reason: Criterion unfolds to all width, local satisfiability, expansion and parameter assumptions, without assuming any closure property
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Lemma 3.2, printed p. 9, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

theorem closure_largest_maximizer
    {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D)
    (T : Finset (Fin n)) (hT : (T.card : ℝ) ≤ D) :
    MaximizesDeficiency F s T (closure F s T) ∧
    ((closure F s T).card : ℝ) < s ∧
    (∀ A, MaximizesDeficiency F s T A → A ⊆ closure F s T) ∧
    (∃! A : CNF n, MaximizesDeficiency F s T A ∧
      ∀ B, MaximizesDeficiency F s T B → B ⊆ A) := by sorry

end RandomCNFDeficiency.LowerBound
