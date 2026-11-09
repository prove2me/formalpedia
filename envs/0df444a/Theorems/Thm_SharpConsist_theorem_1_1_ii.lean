-- Prove2me | Theorems.Thm_SharpConsist_theorem_1_1_ii
-- name    : SharpConsist.theorem_1_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:49.53304+00:00
-- url     : https://prove2.me/theorems/9dfa5be8-180a-48b8-a492-f3612984c3fd
-- title:
--   Theorem 1.1(ii) — no fixed improvement over $2-\sqrt2$ with $e^{o(k)}$ queries and $o(k)$ recourse
-- statement:
--   Let $\beta=2-\sqrt2$. For every $\zeta>0$ there are constants $c_\zeta,d_\zeta>0$ such that the following holds for all sufficiently large integers $k$. There is a stream length $n$ with $n+1\le d_\zeta k$ such that every randomized value-oracle algorithm that, on every model instance with $n+1$ elements (arrival order $1,\dots,n,r$) and every outcome of its randomness, makes at most $Q\le e^{c_\zeta k}$ queries before the last arrival, keeps at most $k$ elements, and satisfies $|S_{n+1}\triangle S_n|\le C\le c_\zeta k$, admits a normalized monotone submodular objective $f$ on $X\cup\{r\}$, fixed independently of the algorithm's random choices, with
--   $$\mathbb Ef(S_{n+1})<(\beta+\zeta)\,\mathrm{OPT}_k(X\cup\{r\}).$$
--   Queries and computation after the last arrival may be unrestricted.
--
--   Together with the algorithmic part (i) of Theorem 1.1, this shows that $2-\sqrt2$ is the sharp approximation threshold for consistent monotone submodular maximization with subexponentially many value queries and sublinear recourse.
--
--   Differences from the source:
--   - generalization: an online algorithm whose queries at time t lie in X_t, with at most Q queries before the last arrival → one adaptive query rule over all subsets of X with Q query slots (NonmonotoneSubmod.QueryLB.DetAlg) per seed; reason: every online algorithm collapses to such a rule; the Lean class contains every paper algorithm
--   - generalization: no advance knowledge of the stream length → the algorithm is indexed by n and knows the arrival order 1, …, n, r; reason: a larger algorithm class; every paper algorithm is one of these
--   - generalization: capacity, recourse and query bounds at every time t on every model instance (of at most d_ζ k elements) → ConsistentAlg.Valid: bounds only on (n+1)-element instances in index order and only at times n and n+1; reason: weaker hypotheses on the algorithm, so the Lean statement implies the paper's
--   - generalization: queries and computation after the final arrival are unrestricted → post sees the whole objective f (including the hidden set); reason: full access subsumes any post-arrival query strategy
--   - reading: E f(S_t) over the algorithm's randomness → Bochner integral over a seed space Ω with a probability measure; Valid requires {ω | S⁺(ω) = s} measurable for every s; reason: the expectation presupposes that the output is a random variable; nothing else is assumed (no measurability of the pre-arrival rule)
--   - encoding: at most Q queries and almost-sure termination on every valid instance → exactly Q query slots, finite by construction; reason: an algorithm that stops early pads with dummy queries; changing a run on a null set of seeds changes no expectation
--   - encoding: ground set X ∪ {r} with X = [n] = {1, …, n}; f : 2^V → ℝ≥0 → Fin (n+1), X = image of Fin n under Fin.castSucc, r = Fin.last n; f real valued; reason: 0-based indices; nonnegativity follows from f(∅) = 0 and monotonicity
--   - generalization: "there exists an instance with a stream of at most d_ζ k elements", chosen after the algorithm → ∃ n with n + 1 ≤ d_ζ k chosen before the algorithm, then ∀ algorithm ∃ f on Fin (n+1); reason: the Lean order ∃ n ∀ alg ∃ f implies the source's ∀ alg ∃ instance, since a paper algorithm restricts to one on the chosen size
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, Theorem 1.1(ii), p.2

import Mathlib
import Definitions.Def_SharpConsist_ConsistentAlg_Valid
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_OPTk

universe u

namespace SharpConsist

/-- **Theorem 1.1(ii) (matching lower bound).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular
Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §1.1, Theorem 1.1(ii), p.2;
β = 2 − √2.

For every `ζ > 0` there are constants `c_ζ, d_ζ > 0` such that for all sufficiently large `k` there is
a stream length `n` with `n + 1 ≤ d_ζ k` for which: every randomized value-oracle algorithm on the
stream `1, …, n, r` that, on every model instance with `n + 1` elements and every outcome of its
randomness, makes at most `Q ≤ e^{c_ζ k}` queries before the last arrival, keeps at most `k` elements and
changes at most `C ≤ c_ζ k` elements at the last arrival, admits a normalized monotone submodular
objective `f` on `X ∪ {r}`, fixed independently of the algorithm's random choices, with
`E f(S_{n+1}) < (2 − √2 + ζ) OPT_k(X ∪ {r})`. Queries and computation after the last arrival are
unrestricted.

**Formalization Note.** The algorithm class (`ConsistentAlg`, `Valid`) is larger than the paper's:
one adaptive pre-arrival rule with `Q` query slots, knowledge of `n`, hypotheses only on
`(n+1)`-element instances in the order `1, …, n, r` and only at times `n`, `n + 1`, and full access to
`f` after `r`. A normalized monotone submodular objective is `PolyContract.IsRankFunction f`
(lattice-form submodularity; real valued, nonnegativity follows). -/
theorem theorem_1_1_ii :
    ∀ ζ : ℝ, 0 < ζ → ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∃ n : ℕ, ((n : ℝ) + 1 ≤ d * (k : ℝ)) ∧
      ∀ (Q C : ℕ), (Q : ℝ) ≤ Real.exp (c * (k : ℝ)) → (C : ℝ) ≤ c * (k : ℝ) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (alg : ConsistentAlg n Q Ω), alg.Valid k C →
        ∃ f : Finset (Fin (n + 1)) → ℝ, PolyContract.IsRankFunction f ∧
          ∫ ω, f (alg.post ω f) ∂μ < (2 - Real.sqrt 2 + ζ) * OPTk k f := by sorry

end SharpConsist
