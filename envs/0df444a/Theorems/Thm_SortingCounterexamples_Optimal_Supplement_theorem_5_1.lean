-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_Supplement_theorem_5_1
-- name    : SortingCounterexamples.Optimal.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:05.152194+00:00
-- url     : https://prove2.me/theorems/af5c5133-1eb8-4585-a5d7-c52ae548ae36
-- title:
--   Theorem 5.1 — every $d$-dimensional geometric class is learnable with $O(d^2\log n+dk)$ queries by a deterministic learner that does not know $k$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $n\ge2$ and $d\ge0$, let $v_1,\dots,v_n\in\mathbb R^d$, and let $H$ be a finite class of rankings of the $n$ items such that every $\pi\in H$ is induced by some direction $w\in\mathbb R^d$ (that is, $i\prec_\pi j\iff\langle v_i,w\rangle<\langle v_j,w\rangle$). Then there is a deterministic learner $A$, which may depend on $n$, $d$, $H$ and $v$ but not on $k$, whose queries are arbitrary linear orders of the items (not necessarily in $H$), such that for every $k\ge0$, every target $\sigma\in H$ and every adaptive oracle whose counterexamples to $A$ include at most $k$ untruthful ones for $\sigma$, $A$ obtains approval after
--   $$Q(A)\ \le\ C\,(d^2\log n+dk)$$
--   queries, the approved query included.
--
--   This is the upper half of Theorem 1.2: in a low-dimensional geometric class the number of queries depends on the dimension $d$ and only logarithmically on $n$.
--
--   **Formalization Note** The query count lives in $\{1,2,\dots\}\cup\{\infty\}$, with $\infty$ when the oracle never approves, so the bound also asserts termination. For $d=0$ and $n\ge2$ no strict ranking is induced and the statement is vacuous, as in the source.
--
--   Differences from the source:
--   - reading: O(d² log n + dk) for n items, no explicit domain → n ≥ 2, every d and every k ≥ 0; reason: at n = 1 the rate d² log 1 + dk vanishes for k = 0 while one query is always made; the base goal uses the same domain
--   - encoding: can be learned using O(d² log n + dk) queries → ∃ C > 0 before n, d, v, H; a learner chosen after H and v and before k, σ and the oracle with Q ≤ ofReal (C · (d² log n + d k)); reason: this is the meaning of an O bound uniform in all parameters for a learner that does not know k; natural logarithm
--   - encoding: at most k untruthful counterexamples → every transcript of the run of A against the oracle has at most k lies for σ; reason: this is exactly every adaptive response path with at most k lies against the deterministic learner
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 22 / PDF p. 23, Theorem 5.1 (proof to printed p. 25 / PDF p. 26); upper half of Theorem 1.2, printed p. 4 / PDF p. 5; model printed p. 1 / PDF p. 2

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol
import Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric

open scoped ENNReal

namespace SortingCounterexamples.Optimal.Supplement

open SortingCounterexamples.Optimal

/-- Theorem 5.1: there is an absolute `C > 0` such that for every `n ≥ 2`, every `d`, every
`d`-dimensional geometric class `H` of rankings of `n` items with representation `v`, there is
one deterministic learner (its queries are arbitrary linear orders, not necessarily in `H`),
chosen before and independently of `k`, which for every `k`, every target `σ ∈ H` and every
oracle returning at most `k` untruthful counterexamples along the run obtains approval within
`C (d² log n + d k)` queries. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ), 2 ≤ n → ∀ (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n)),
      IsGeometricClass v H → ∃ A : DetLearner n, ∀ k : ℕ, ∀ σ ∈ H, ∀ O : Oracle n,
        RunAdmissible A O σ k →
          ((queries A O : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (C * upperRate n d k) := by sorry

end SortingCounterexamples.Optimal.Supplement
