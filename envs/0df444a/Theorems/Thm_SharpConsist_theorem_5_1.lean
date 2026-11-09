-- Prove2me | Theorems.Thm_SharpConsist_theorem_5_1
-- name    : SharpConsist.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:33.646828+00:00
-- url     : https://prove2.me/theorems/b86f0501-090e-4b07-8ceb-dac2ba36af59
-- title:
--   Theorem 5.1 — finite bound (5.1), unique minimizer and small marginals (asymptotic clause: theorem_5_1_asymptotic)
-- statement:
--   This item is Theorem 5.1 without its asymptotic clause, which is the companion item `SharpConsist.theorem_5_1_asymptotic`.
--
--   1. **Finite bound (5.1).** Fix $T\in[7/5,3/2]$, integers $m\ge32$, $k\ge10$, $n=(m+1)k$, and $R(T)=(T^2+2)/(T^2+2T+2)$. Consider any randomized value-oracle algorithm on the stream $1,2,\dots,n,r$ (seed space $\Omega$ with a probability measure) that, on every model instance with $n+1$ elements and every random outcome, makes at most $Q$ queries before the final arrival, keeps at most $k$ elements, and makes at most $C$ symmetric changes at the final arrival. Then for some $k$-set $A\subseteq X=[n]$, the function $f_A$ of Eq. (5.9) is normalized, monotone and submodular on $X\cup\{r\}$ and
--   $$\mathbb Ef_A(S_{n+1})\le\Bigl(\frac{R(T)+38/m+5C/k}{1-5/k}+2(Q+1)e^{-k/(8192m^2)}\Bigr)\mathrm{OPT}_k(X\cup\{r\}).$$
--   2. **Unique minimizer.** $R(\sqrt2)=2-\sqrt2$, and for every $T\in[7/5,3/2]$, $R(\sqrt2)\le R(T)$ with equality only for $T=\sqrt2$.
--   3. **Small marginals.** For every such $T,m,k,n$ and $k$-set $A$, every old element has marginal at most $5/k$ in $f_A$ on every background, with or without $r$.
--
--   The instance is fixed before the algorithm's random choices, over which the expectation is taken; queries before $r$ may adaptively use any subset of arrived elements, and queries and computation after $r$ are unrestricted.
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
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5, Theorem 5.1, p.12

import Mathlib
import Definitions.Def_SharpConsist_ConsistentAlg_Valid
import Definitions.Def_SharpConsist_fA
import Definitions.Def_SharpConsist_OPTk
import Definitions.Def_SharpConsist_RT

universe u

namespace SharpConsist

/-- **Theorem 5.1 (finite query–recourse lower bound): the finite bound (5.1), the unique minimizer,
and the small-marginal clause.** The asymptotic clause of Theorem 5.1 is the companion item
`SharpConsist.theorem_5_1_asymptotic`. Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular
Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5, Theorem 5.1, p.12.

Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 10`, `n = (m+1)k`. For every randomized algorithm on the
stream `1, …, n, r` (seed space `Ω` with a probability measure `μ`) that makes `Q` queries before the
final arrival and keeps at most `k` elements with at most `C` symmetric changes at the final arrival on
every model instance with `n + 1` elements, there is a `k`-set `A ⊆ X` such that the function `f_A` of Eq. (5.9) is normalized, monotone and
submodular and
`E f_A(S_{n+1}) ≤ ((R(T) + 38/m + 5C/k)/(1 − 5/k) + 2(Q+1)e^{−k/(8192m²)}) OPT_k(X ∪ {r})`.
Moreover `R(√2) = 2 − √2` and `T = √2` is the unique minimizer of `R` on `[7/5, 3/2]`, and current
elements have marginals at most `5/k` on all backgrounds, with or without `r`.

**Formalization Note.** The instance is the constructed `f_A` of Eq. (5.9); the expectation is the integral over the seed, and `Valid` makes the
integrand a random variable. -/
theorem theorem_5_1 :
    (∀ (T : ℝ), T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2) → ∀ (m k n : ℕ), 32 ≤ m → 10 ≤ k →
      n = (m + 1) * k →
      ∀ (Q C : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (alg : ConsistentAlg n Q Ω), alg.Valid k C →
        ∃ A : Finset (Fin n), A.card = k ∧ PolyContract.IsRankFunction (fA T m k A) ∧
          ∫ ω, fA T m k A (alg.post ω (fA T m k A)) ∂μ ≤
            ((RT T + 38 / (m : ℝ) + 5 * (C : ℝ) / (k : ℝ)) / (1 - 5 / (k : ℝ)) +
              2 * ((Q : ℝ) + 1) * Real.exp (-((k : ℝ) / (8192 * (m : ℝ) ^ 2)))) *
              OPTk k (fA T m k A)) ∧
    (RT (Real.sqrt 2) = 2 - Real.sqrt 2 ∧
      ∀ T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2), RT (Real.sqrt 2) ≤ RT T ∧
        (RT T = RT (Real.sqrt 2) → T = Real.sqrt 2)) ∧
    (∀ (T : ℝ), T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2) → ∀ (m k n : ℕ), 32 ≤ m → 10 ≤ k →
      n = (m + 1) * k → ∀ A : Finset (Fin n), A.card = k →
      ∀ (e : Fin n) (U : Finset (Fin (n + 1))), Fin.castSucc e ∉ U →
        fA T m k A (insert (Fin.castSucc e) U) - fA T m k A U ≤ 5 / (k : ℝ)) := by sorry

end SharpConsist
