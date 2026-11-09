-- Prove2me | Theorems.Thm_SharpConsist_theorem_5_1_asymptotic
-- name    : SharpConsist.theorem_5_1_asymptotic
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:40.980719+00:00
-- url     : https://prove2.me/theorems/95ffee37-79c3-450e-b718-55fa950ed489
-- title:
--   Theorem 5.1 — asymptotic clause (finite clauses: theorem_5_1)
-- statement:
--   This item is the asymptotic clause of Theorem 5.1; the finite bound, the minimizer and the marginal clause are the companion item `SharpConsist.theorem_5_1`.
--
--   For every $\zeta>0$ there are an integer $m\ge32$ and constants $c_\zeta,d_\zeta>0$ such that, for all sufficiently large $k$, with $n=(m+1)k$:
--
--   1. $n+1\le d_\zeta k$, and
--   2. every randomized value-oracle algorithm on the stream $1,\dots,n,r$ whose bounds $Q\le e^{c_\zeta k}$ (queries before the final arrival) and $C\le c_\zeta k$ (symmetric changes there), together with the capacity $k$, hold on every model instance with $n+1$ elements and every random outcome has a fixed $k$-set $A\subseteq X$ for which $f_A$ (Eq. (5.9) with $T=\sqrt2$) is normalized, monotone and submodular and
--   $$\mathbb Ef_A(S_{n+1})<(2-\sqrt2+\zeta)\,\mathrm{OPT}_k(X\cup\{r\}).$$
--
--   The instance may depend on the algorithm but is fixed before its random choices.
--
--   Differences from the source:
--   - generalization: an online algorithm whose queries at time t lie in X_t, with at most Q queries before the last arrival → one adaptive query rule over all subsets of X with Q query slots (NonmonotoneSubmod.QueryLB.DetAlg) per seed; reason: every online algorithm collapses to such a rule; the Lean class contains every paper algorithm
--   - generalization: no advance knowledge of the stream length → the algorithm is indexed by n and knows the arrival order 1, …, n, r; reason: a larger algorithm class; every paper algorithm is one of these
--   - generalization: capacity, recourse and query bounds at every time t on every model instance (of at most d_ζ k elements) → ConsistentAlg.Valid: bounds only on (n+1)-element instances in index order and only at times n and n+1; reason: weaker hypotheses on the algorithm, so the Lean statement implies the paper's
--   - generalization: queries and computation after the final arrival are unrestricted → post sees the whole objective f (including the hidden set); reason: full access subsumes any post-arrival query strategy
--   - reading: E f(S_t) over the algorithm's randomness → Bochner integral over a seed space Ω with a probability measure; Valid requires {ω | S⁺(ω) = s} measurable for every s; reason: the expectation presupposes that the output is a random variable; nothing else is assumed (no measurability of the pre-arrival rule)
--   - encoding: at most Q queries and almost-sure termination on every valid instance → exactly Q query slots, finite by construction; reason: an algorithm that stops early pads with dummy queries; changing a run on a null set of seeds changes no expectation
--   - encoding: ground set X ∪ {r} with X = [n] = {1, …, n}; f : 2^V → ℝ≥0 → Fin (n+1), X = image of Fin n under Fin.castSucc, r = Fin.last n; f real valued; reason: 0-based indices; nonnegativity follows from f(∅) = 0 and monotonicity
--   - reading: "for some k-set A and normalized monotone submodular f_A on X ∪ {r}" (stated before the construction) → the function f_A of Eq. (5.9) for some k-set A, with PolyContract.IsRankFunction f_A in the conclusion; reason: f_A in Theorem 5.1 is the instance constructed in §5.2; the Lean statement implies the existential one
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5, Theorem 5.1, p.12; proof on p.17

import Mathlib
import Definitions.Def_SharpConsist_ConsistentAlg_Valid
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_fA
import Definitions.Def_SharpConsist_OPTk

universe u

namespace SharpConsist

/-- **Theorem 5.1, asymptotic clause.** The finite bound, the minimizer and the marginal clause of
Theorem 5.1 are the companion item `SharpConsist.theorem_5_1`. Fu–Zhang–Tao, *A Sharp Barrier of
Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5,
Theorem 5.1, p.12; proved on p.17.

For every `ζ > 0` there are an integer `m ≥ 32` and constants `c_ζ, d_ζ > 0` such that for all
sufficiently large `k`, with `n = (m+1)k`: `n + 1 ≤ d_ζ k`, and every randomized algorithm on the
stream `1, …, n, r` whose bounds `Q ≤ e^{c_ζ k}` (queries before the final arrival) and `C ≤ c_ζ k`
(symmetric changes at it) hold on every model instance with `n + 1` elements has a fixed `k`-set `A` for which
`f_A` (Eq. (5.9) at `T = √2`) is normalized, monotone and submodular and `E f_A(S_{n+1}) < (2 − √2 + ζ) OPT_k(X ∪ {r})`.

**Formalization Note.** The instance `f_A` (with its `A`) is chosen after the algorithm and before the
expectation over the seed, so it is fixed independently of the algorithm's random choices. -/
theorem theorem_5_1_asymptotic :
    ∀ ζ : ℝ, 0 < ζ → ∃ m : ℕ, 32 ≤ m ∧ ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (((m + 1) * k : ℕ) : ℝ) + 1 ≤ d * (k : ℝ) ∧
      ∀ (Q C : ℕ), (Q : ℝ) ≤ Real.exp (c * (k : ℝ)) → (C : ℝ) ≤ c * (k : ℝ) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (alg : ConsistentAlg ((m + 1) * k) Q Ω),
        alg.Valid k C →
        ∃ A : Finset (Fin ((m + 1) * k)), A.card = k ∧ PolyContract.IsRankFunction (fA (Real.sqrt 2) m k A) ∧
          ∫ ω, fA (Real.sqrt 2) m k A (alg.post ω (fA (Real.sqrt 2) m k A)) ∂μ <
            (2 - Real.sqrt 2 + ζ) * OPTk k (fA (Real.sqrt 2) m k A) := by sorry

end SharpConsist
