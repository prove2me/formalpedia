-- Prove2me | Theorems.Thm_SharpConsist_Supplement_theorem_8_1
-- name    : SharpConsist.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:25:16.05434+00:00
-- url     : https://prove2.me/theorems/851e0578-5d11-4262-b8a0-dc0f57740c9e
-- title:
--   Theorem 8.1 — sharp threshold $1-(\sqrt2-1)\vartheta$ under curvature $\le\vartheta$ (algorithm and matching lower bound)
-- statement:
--   Let $\rho_\vartheta=1-(\sqrt2-1)\vartheta$. Total curvature at most $\vartheta$ means $f(S\cup\{i\})-f(S)\ge(1-\vartheta)f(\{i\})$ for all $S$ and $i\notin S$, over the entire stream.
--
--   1. **Algorithm.** There is a constant $K>0$ such that for every known $\vartheta\in[0,1]$ and every $\varepsilon>0$ there are a randomized online algorithm and a polynomial bound $c\,(t+k+1)^d$ such that, on every stream whose normalized monotone submodular objective has total curvature at most $\vartheta$, for every $k\ge1$ and every arrival $t$: on every outcome arrival $t$ makes at most $c\,(|X_t|+k+1)^d$ current value queries, $|S_t|\le k$ and $|S_t\triangle S_{t-1}|\le K\varepsilon^{-2}$; and $S_t$ is a random variable with
--   $$\mathbb E f(S_t)\ \ge\ (\rho_\vartheta-\varepsilon)\,\mathrm{OPT}_k(X_t).$$
--   2. **Sharpness.** For every $\vartheta\in(0,1]$ and $\zeta>0$ there are $c,d>0$ such that for all sufficiently large $k$ there is a stream length $n$ with $n+1\le dk$ for which the following holds. Consider any randomized algorithm on the stream $1,\dots,n,r$ that, on every instance with $n+1$ elements of curvature at most $\vartheta$ and every random outcome, makes at most $e^{ck}$ queries before the final arrival, keeps at most $k$ elements, and makes at most $ck$ symmetric changes at the final arrival. Then some normalized monotone submodular $f$ on $X\cup\{r\}$ of curvature at most $\vartheta$, fixed independently of the algorithm's randomness, has
--   $$\mathbb E f(S_{n+1})\ <\ (\rho_\vartheta+\zeta)\,\mathrm{OPT}_k(X\cup\{r\}),$$
--   that is, expected approximation ratio below $\rho_\vartheta+\zeta$, even with unrestricted queries and computation after the final arrival.
--
--   At $\vartheta=1$ the threshold is $2-\sqrt2$ (Theorem 1.1); at $\vartheta=0$ it is $1$.
--
--   Differences from the source:
--   - encoding: a finite ground set V whose elements arrive one at a time; X_t the first t arrivals → V = Fin N with element i the (i+1)-st arrival, X_t = {0, …, t−1}, objectives read on sets of arrival indices (natFn), OPT_k(X_t) = optAt k F t; reason: the algorithm sees the objective only through its values, so naming elements by arrival index changes no instance
--   - encoding: a randomized algorithm using polynomially many current value queries per arrival (no claim about computation) → OnlineAlg: a seed space (Ω, μ) chosen with the algorithm, computation and sampling free, queries on subsets of X_t counted; per-arrival query count ≤ c(t + k + 1)^d with c, d depending only on the theorem's parameters; reason: the theorem bounds queries only; a polynomial in |X_t| and k is exactly a bound c(t+k+1)^d
--   - reading: O(ε^{-2}) worst-case symmetric recourse (for each known ϑ) → recourse ≤ K/ε² with one K fixed before ϑ and ε; reason: the stronger reading of O(·); the proof's bound 8⌈16/ε⌉²+2 does not depend on ϑ
--   - generalization: lower bound against algorithms of the paper's online model, with hypotheses on every instance of at most dk elements with curvature at most ϑ → against every SharpConsist.ConsistentAlg (one adaptive pre-arrival rule with Q ≤ e^{ck} slots that knows n; output after r with full access to f), whose conditions CurvValid are assumed only on curvature-≤ϑ instances with n + 1 elements, for a stream length n with n + 1 ≤ dk chosen before the algorithm; reason: every algorithm of the paper's model satisfying the page's hypotheses is such an algorithm, so the Lean clause specializes to the page's
--   - encoding: expected approximation ratio E f(S_{n+1}) / OPT_k less than ρ_ϑ + ζ → ∫ f(S⁺) dμ < (ρ_ϑ + ζ)·OPT_k f; reason: equivalent when OPT_k > 0, which the strict inequality forces since f ≥ 0
--   - encoding: (lower bound) the expectation E f(S_{n+1}) over the algorithm's randomness → CurvValid also assumes that {ω | S⁺(ω) = s} is measurable for every s on every curvature-≤ϑ instance, as the published ConsistentAlg.Valid does; reason: the page's expectation presupposes that S_{n+1} is a random variable; it excludes no algorithm for which the page's expectation is defined
--   - encoding: bounds for every outcome of the randomness; almost-sure termination after every arrival → query, capacity and recourse bounds (and termination within the budget) required for every seed; reason: worst case over seeds as on the page; requiring it on null sets too only restricts the algorithm
--   - encoding: E f(S_t), an expectation over the algorithm's randomness → the conclusion also asserts that {ω | S_t(ω) = S} is measurable for every S, and the expectation is the integral over the seed (tape) law; reason: makes the expectation genuine; it only adds to what the algorithm must satisfy
--   - encoding: integer capacity k ≥ 1 (p.1) → hypothesis 1 ≤ k; reason: the model's standing assumption
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §8, Theorem 8.1, pp.24–25; Lemma D.1, p.39

import Mathlib
import Definitions.Def_SharpConsist_ConsistentAlg
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_OPTk
import Definitions.Def_SharpConsist_Supplement_natFn
import Definitions.Def_SharpConsist_Supplement_optAt
import Definitions.Def_SharpConsist_Supplement_HasCurvatureAtMost
import Definitions.Def_SharpConsist_Supplement_OnlineAlg
import Definitions.Def_SharpConsist_Supplement_CurvValid

universe u

namespace SharpConsist.Supplement

/-- **Theorem 8.1 (sharp threshold under bounded curvature), both clauses.** Fu–Zhang–Tao, *A Sharp
Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…),
§8, Theorem 8.1, pp.24–25; `ρ_ϑ = 1 − (√2 − 1)ϑ`.

**(Upper bound.)** There is a constant `K > 0` such that for every known `ϑ ∈ [0, 1]` and every
`ε > 0` there are a randomized online value-oracle algorithm (seed space `(Ω, μ)`) and a polynomial
bound `c (t + k + 1)^d` such that, on every stream `V = Fin N` whose objective `f` is normalized
monotone submodular with total curvature at most `ϑ` over the entire stream, every `k ≥ 1`, every
`t ≤ N` and every seed: arrival `t` makes at most `c (t + k + 1)^d` value queries, `|S_t| ≤ k` and
`|S_t △ S_{t−1}| ≤ K ε⁻²`; and `S_t` is a random variable with `E f(S_t) ≥ (ρ_ϑ − ε) OPT_k(X_t)`.

**(Sharpness.)** For every `ϑ ∈ (0, 1]` and `ζ > 0` there are `c, d > 0` such that for all
sufficiently large `k` there is a stream length `n` with `n + 1 ≤ d k` for which: every randomized
algorithm on the stream `1, …, n, r` that, on every instance with `n + 1` elements of curvature at most
`ϑ` and every random outcome, makes at most `Q ≤ e^{c k}` queries before the final arrival, keeps at
most `k` elements and makes at most `C ≤ c k` symmetric changes at the final arrival, admits a
normalized monotone submodular `f` on `X ∪ {r}` of total curvature at most `ϑ` (including the final
element), fixed independently of the algorithm's randomness, with
`E f(S_{n+1}) < (ρ_ϑ + ζ) OPT_k(X ∪ {r})` (expected approximation ratio below `ρ_ϑ + ζ`). Queries and
computation after the final arrival are unrestricted.

**Formalization Note.** Upper bound: elements are arrival indices (`natFn`), the algorithm may
depend on `ϑ` and `ε`, only queries are counted, `O(ε⁻²)` is read with one `K` fixed before `ϑ` and
`ε`. Sharpness: the algorithm class is the published `SharpConsist.ConsistentAlg` (one adaptive
pre-arrival rule with `Q` slots, knowledge of `n`, full access to `f` after `r`), larger than the
paper's, and its conditions (`CurvValid`) are assumed only on curvature-`≤ ϑ` instances with `n + 1`
elements; the strict inequality forces `OPT_k > 0`, so the ratio is defined. -/
theorem theorem_8_1 :
    (∃ K : ℝ, 0 < K ∧ ∀ ϑ : ℝ, 0 ≤ ϑ → ϑ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
        MeasureTheory.IsProbabilityMeasure μ ∧ ∃ (A : OnlineAlg Ω) (c d : ℕ),
        ∀ (N : ℕ) (f : Finset (Fin N) → ℝ), PolyContract.IsRankFunction f →
          HasCurvatureAtMost ϑ f →
        ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ N →
          (∀ ω : Ω, A.QueriesAtMost ω k (natFn f) (fun _ => 0) t (c * (t + k + 1) ^ d)) ∧
          (∀ ω : Ω, (A.out ω k (natFn f) (fun _ => 0) t).card ≤ k ∧
            ((symmDiff (A.out ω k (natFn f) (fun _ => 0) t)
              (A.out ω k (natFn f) (fun _ => 0) (t - 1))).card : ℝ) ≤ K / ε ^ 2) ∧
          (∀ S : Finset ℕ, MeasurableSet {ω | A.out ω k (natFn f) (fun _ => 0) t = S}) ∧
          (1 - (Real.sqrt 2 - 1) * ϑ - ε) * optAt k (natFn f) t ≤
            ∫ ω, natFn f (A.out ω k (natFn f) (fun _ => 0) t) ∂μ) ∧
    (∀ ϑ : ℝ, 0 < ϑ → ϑ ≤ 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      ∃ n : ℕ, ((n : ℝ) + 1 ≤ d * (k : ℝ)) ∧
      ∀ (Q C : ℕ), (Q : ℝ) ≤ Real.exp (c * (k : ℝ)) → (C : ℝ) ≤ c * (k : ℝ) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (alg : SharpConsist.ConsistentAlg n Q Ω),
        CurvValid alg ϑ k C →
        ∃ f : Finset (Fin (n + 1)) → ℝ, PolyContract.IsRankFunction f ∧
          HasCurvatureAtMost ϑ f ∧
          ∫ ω, f (alg.post ω f) ∂μ < (1 - (Real.sqrt 2 - 1) * ϑ + ζ) * SharpConsist.OPTk k f) := by sorry

end SharpConsist.Supplement
