-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_random_local_satisfiability_expansion
-- name    : RandomCNFDeficiency.LowerBound.random_local_satisfiability_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:33.854978+00:00
-- url     : https://prove2.me/theorems/d8791487-b6b0-46b5-bd76-1d4531165dcc
-- title:
--   Proposition 3.8 — random formula criterion
-- statement:
--   For every integer sequence $k(n)\to\infty$ with $k(n)=O(\log_2 n)$, sample $M=n2^{k(n)}$ independent uniform signed clauses of width $k(n)$ with replacement. Set $s=n/\sqrt{k(n)}$ and $D=n/2-4n/\sqrt{k(n)}$. Let $E$ be the event that the sampled CNF is unsatisfiable, has width at most $D$, and satisfies both entire conditions of Theorem 3.1, with $s\ge1$ and $2\le D\le n$. Then
--
--   $$\Pr(E)\longrightarrow1,\qquad
--   \Pr(E)\ge1-e^{-(1-\ln2)n}-\frac{e^{-k(n)^2}}{1-e^{-k(n)}}-ne^{-(3/2-\ln2)n}\quad\text{eventually}.$$
--
--   The theorem also records the eventual guards $2\le k(n)\le n$, $k(n)\le D$, $s\ge1$, and $2s<n$. This supplies the random local satisfiability and expansion conclusions, rather than assuming them.
--
--   Differences from the source:
--   - encoding: variables indexed by [n] with Boolean value 1 true → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - encoding: ω_n(1) ≤ k ≤ O(log n) and probability 1-o_n(1) → every sequence k tending to infinity with some fixed C>0 giving an eventual k(n) ≤ C log₂ n, and probability tending to 1; reason: eventual 1 ≤ k(n) ≤ n follows from this regime and makes the finite sampling space nonempty; no fixed growth speed is imposed
--   - encoding: M=n2^k iid uniform signed clauses sampled with replacement → uniform counting probability on the published ordered M-tuple type, followed by deletion of repeats for deterministic CNF predicates; reason: every k-support has exactly 2^k signs; taking the image preserves satisfaction and allowed PC input polynomials
--   - generalization: Proposition 3.8 states probability 1-o_n(1) → probability tends to 1 and eventually is at least 1-ε(n,k), with the full eventual parameter guards; reason: Equation (32) explicitly proves this stronger estimate; forgetting the eventual estimate recovers the proposition
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Proposition 3.8 and Equation (21), printed p. 12, PDF p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf; Equation (32), printed p. 14, PDF p. 16

import Definitions.Def_RandomCNFDeficiency_LowerBound_RandomModel
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

theorem random_local_satisfiability_expansion
    (k : ℕ → ℕ) (hk : LogarithmicRegime k) :
    Filter.Tendsto (fun n => sampleProbability n (k n) (CriterionEvent n (k n)))
      Filter.atTop (nhds 1) ∧
    (∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ k n ∧ k n ≤ n ∧ (k n : ℝ) ≤ degreeThreshold n (k n) ∧
      1 ≤ smallThreshold n (k n) ∧ 2 * smallThreshold n (k n) < (n : ℝ) ∧
      1 - failureBound n (k n) ≤ sampleProbability n (k n) (CriterionEvent n (k n))) := by sorry

end RandomCNFDeficiency.LowerBound
