-- Prove2me | Theorems.Thm_SharpConsist_Supplement_theorem_8_2
-- name    : SharpConsist.Supplement.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:26:02.411003+00:00
-- url     : https://prove2.me/theorems/7be118ba-4ed0-443a-bfd8-09565e9bdb9f
-- title:
--   Theorem 8.2 — preserving a modular component: $\max\{\ell(O)+\beta g(O)\}-\varepsilon\,\mathrm{OPT}_k$ with $O(\varepsilon^{-2})$ recourse
-- statement:
--   Let $\beta=2-\sqrt2$ and suppose $f=g+\ell$ on $2^V$, where $g$ is normalized monotone submodular, accessed through current value queries, and $\ell(S)=\sum_{i\in S}\ell_i$ is nonnegative modular, with the weight $\ell_i$ revealed when $i$ arrives.
--
--   There is a constant $K>0$ such that for every $\varepsilon>0$ there are a randomized online algorithm and a polynomial bound $c\,(t+k+1)^d$ such that, for every such stream, every capacity $k\ge1$ and every arrival $t$:
--
--   1. on every outcome, arrival $t$ makes at most $c\,(|X_t|+k+1)^d$ current value queries, $|S_t|\le k$ and $|S_t\triangle S_{t-1}|\le K\varepsilon^{-2}$;
--   2. $S_t$ is a random variable and, at each fixed time $t$,
--   $$\mathbb E f(S_t)\ \ge\ \max_{O\subseteq X_t,\ |O|\le k}\{\ell(O)+\beta g(O)\}-\varepsilon\,\mathrm{OPT}_k(f,X_t).\tag{8.2}$$
--
--   The same comparison set $O$ appears in both terms, so the modular part keeps coefficient one. Applied with $\ell_i=(1-\vartheta)f(\{i\})$ this yields the algorithmic part of Theorem 8.1.
--
--   Differences from the source:
--   - encoding: a finite ground set V whose elements arrive one at a time; X_t the first t arrivals → V = Fin N with element i the (i+1)-st arrival, X_t = {0, …, t−1}, objectives read on sets of arrival indices (natFn), OPT_k(X_t) = optAt k F t; reason: the algorithm sees the objective only through its values, so naming elements by arrival index changes no instance
--   - encoding: g accessed through current value queries; ℓ_i available when i arrives; polynomially many queries per arrival → OnlineAlg whose oracle answers values of g on subsets of X_t and whose side information at arrival t is the list ℓ_0, …, ℓ_{t−1}; computation and sampling free; per-arrival query count ≤ c(t+k+1)^d; reason: queries of f and of g are interchangeable once ℓ on current sets is known; the theorem bounds queries only
--   - reading: O(ε^{-2}) worst-case symmetric recourse → recourse ≤ K/ε² with one K fixed before ε; reason: the stronger reading of O(·); the proof gives 8⌈16/ε⌉²+2
--   - encoding: bounds for every outcome of the randomness; almost-sure termination after every arrival → query, capacity and recourse bounds (and termination within the budget) required for every seed; reason: worst case over seeds as on the page; requiring it on null sets too only restricts the algorithm
--   - encoding: E f(S_t), an expectation over the algorithm's randomness → the conclusion also asserts that {ω | S_t(ω) = S} is measurable for every S, and the expectation is the integral over the seed (tape) law; reason: makes the expectation genuine; it only adds to what the algorithm must satisfy
--   - encoding: integer capacity k ≥ 1 (p.1) → hypothesis 1 ≤ k; reason: the model's standing assumption
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §8.1, Theorem 8.2, Eq. (8.2), p.25; proof p.27

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_Supplement_natFn
import Definitions.Def_SharpConsist_Supplement_optAt
import Definitions.Def_SharpConsist_Supplement_OnlineAlg

namespace SharpConsist.Supplement

/-- **Theorem 8.2 (preserving a modular component).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent
Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §8.1, Theorem 8.2,
Eq. (8.2), p.25; `β = 2 − √2`.

There is a constant `K > 0` such that for every `ε > 0` there are a randomized online value-oracle
algorithm (seed space `(Ω, μ)`) and a polynomial bound `c (t + k + 1)^d` such that, on every stream
`V = Fin N` with objective `f = g + ℓ`, where `g` is normalized monotone submodular, accessed through
value queries, and `ℓ(S) = Σ_{i∈S} ℓ_i` is nonnegative modular with `ℓ_i` revealed when `i` arrives,
for every `k ≥ 1`, every `t ≤ N` and every seed: arrival `t` makes at most `c (t + k + 1)^d` value
queries, `|S_t| ≤ k` and `|S_t △ S_{t−1}| ≤ K ε⁻²`; and `S_t` is a random variable with
`E f(S_t) ≥ max_{O ⊆ X_t, |O| ≤ k} {ℓ(O) + β g(O)} − ε OPT_k(f, X_t)`.

**Formalization Note.** The oracle answers values of `g`; the side information of element `i` is
`ℓ_i` (the list of revealed weights grows by one entry per arrival). Queries of `f` are equivalent,
since `ℓ` on current sets is known. The benchmark uses the same `O` in both terms. Only queries are
counted; `O(ε⁻²)` is read with one constant `K` fixed before `ε`. -/
theorem theorem_8_2 :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
        MeasureTheory.IsProbabilityMeasure μ ∧ ∃ (A : OnlineAlg Ω) (c d : ℕ),
        ∀ (N : ℕ) (g : Finset (Fin N) → ℝ), PolyContract.IsRankFunction g →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) →
        ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ N →
          (∀ ω : Ω, A.QueriesAtMost ω k (natFn g) (fun i => if h : i < N then ℓ ⟨i, h⟩ else 0) t
            (c * (t + k + 1) ^ d)) ∧
          (∀ ω : Ω,
            (A.out ω k (natFn g) (fun i => if h : i < N then ℓ ⟨i, h⟩ else 0) t).card ≤ k ∧
            ((symmDiff (A.out ω k (natFn g) (fun i => if h : i < N then ℓ ⟨i, h⟩ else 0) t)
              (A.out ω k (natFn g) (fun i => if h : i < N then ℓ ⟨i, h⟩ else 0) (t - 1))).card : ℝ)
                ≤ K / ε ^ 2) ∧
          (∀ S : Finset ℕ, MeasurableSet
            {ω | A.out ω k (natFn g) (fun i => if h : i < N then ℓ ⟨i, h⟩ else 0) t = S}) ∧
          optAt k (natFn fun S => (∑ i ∈ S, ℓ i) + (2 - Real.sqrt 2) * g S) t
              - ε * optAt k (natFn fun S => g S + ∑ i ∈ S, ℓ i) t ≤
            ∫ ω, natFn (fun S => g S + ∑ i ∈ S, ℓ i)
              (A.out ω k (natFn g) (fun i => if h : i < N then ℓ ⟨i, h⟩ else 0) t) ∂μ := by sorry

end SharpConsist.Supplement
