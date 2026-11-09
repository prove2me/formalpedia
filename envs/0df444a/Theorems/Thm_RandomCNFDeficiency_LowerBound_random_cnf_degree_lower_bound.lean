-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_random_cnf_degree_lower_bound
-- name    : RandomCNFDeficiency.LowerBound.random_cnf_degree_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:14.990188+00:00
-- url     : https://prove2.me/theorems/4df19722-ea48-4dfe-8db0-ba67d0ea9ced
-- title:
--   Theorem 1.1 — near-half PC degree over every field
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ be any sequence tending to infinity and eventually bounded by $C\log_2 n$ for some fixed $C>0$. On $n$ variables sample exactly $M=n2^{k(n)}$ independent uniformly random signed clauses, each with $k(n)$ distinct variables, with replacement. Write $F_n$ for their conjunction. Then
--
--   $$\Pr\left[F_n\text{ is unsatisfiable and }
--   \forall\text{ fields }K\ \forall\text{ PC refutations }\pi\text{ of }F_n,
--   \ \deg(\pi)>\frac n2-\frac{4n}{\sqrt{k(n)}}\right]\longrightarrow1.$$
--
--   The degree is the maximum ordinary total degree of any line in the finite refutation, with Boolean axioms explicitly allowed. All fields, including characteristic zero and arbitrary extensions, are quantified inside the same event. This is the complete headline lower bound; no satisfiability, expansion or pseudo-reduction existence is assumed.
--
--   Differences from the source:
--   - encoding: variables indexed by [n] with Boolean value 1 true → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - encoding: ω_n(1) ≤ k ≤ O(log n) and probability 1-o_n(1) → every sequence k tending to infinity with some fixed C>0 giving an eventual k(n) ≤ C log₂ n, and probability tending to 1; reason: eventual 1 ≤ k(n) ≤ n follows from this regime and makes the finite sampling space nonempty; no fixed growth speed is imposed
--   - encoding: M=n2^k iid uniform signed clauses sampled with replacement → uniform counting probability on the published ordered M-tuple type, followed by deletion of repeats for deterministic CNF predicates; reason: every k-support has exactly 2^k signs; taking the image preserves satisfaction and allowed PC input polynomials
--   - encoding: degree minimum strictly greater than D → every finite ordinary PC refutation has integer maximum degree, coerced to ℝ, strictly greater than D; reason: for integer derivation degree q, q ≤ D iff q ≤ floor(D); no infimum on an empty family and no loss of one degree
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem 1.1, printed p. 2, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_RandomModel
universe uGoal
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

theorem random_cnf_degree_lower_bound
    (k : ℕ → ℕ) (hk : LogarithmicRegime k) :
    Filter.Tendsto (fun n => sampleProbability n (k n) (HardEvent.{uGoal} n (k n)))
      Filter.atTop (nhds 1) := by sorry

end RandomCNFDeficiency.LowerBound
