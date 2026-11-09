-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_deterministic_degree_lower_bound
-- name    : RandomCNFDeficiency.LowerBound.deterministic_degree_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:23.228189+00:00
-- url     : https://prove2.me/theorems/5471f0cb-4430-474b-a68e-8df3aef03e36
-- title:
--   Theorem 3.1 — deterministic degree criterion
-- statement:
--   Let $F$ be a finite CNF on $n$ variables, $s\ge1$, and $2\le D\le n$. Every clause must have width at most $D$. Suppose (i) every subformula with fewer than $s$ clauses is satisfiable, and (ii) every clause set $A\subseteq F$ with $s\le|A|\le2s$ satisfies $|N(A)|>D+|A|$. Then, simultaneously over every field $K$,
--
--   $$\text{every ordinary PC refutation }\pi\text{ of }F\text{ has }\deg(\pi)>D.$$
--
--   This is the full deterministic criterion, including both hypotheses, the width bound and strict conclusion. The real-threshold extension contains every source integer instance and applies directly to the unrounded random parameters.
--
--   Differences from the source:
--   - encoding: variables indexed by [n] with Boolean value 1 true → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - generalization: integer s ≥ 1 and degree cutoff D in Theorem 3.1 and its standing context → real s ≥ 1 and real 2 ≤ D ≤ n, comparing all cardinalities and degrees in ℝ; reason: the same maximizer and union bounds use only real inequalities; every integer instance is included and Equation (21) is represented without rounding
--   - encoding: degree minimum strictly greater than D → every finite ordinary PC refutation has integer maximum degree, coerced to ℝ, strictly greater than D; reason: for integer derivation degree q, q ≤ D iff q ≤ floor(D); no infimum on an empty family and no loss of one degree
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem 3.1, Equation (13), printed p. 9, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_PolynomialCalculus
import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
universe uCriterion
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

theorem deterministic_degree_lower_bound
    {n : ℕ} (F : CNF n) (s D : ℝ) (hF : Criterion F s D) :
    AllFieldsHard.{uCriterion} F D := by sorry

end RandomCNFDeficiency.LowerBound
