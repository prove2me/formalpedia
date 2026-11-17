-- Prove2me | Theorems.Thm_SharpConsist_Supplement_theorem_7_1
-- name    : SharpConsist.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:24:25.486619+00:00
-- url     : https://prove2.me/theorems/bd6dbf3f-8c26-4e19-8508-936efd549519
-- title:
--   Theorem 7.1 — coverage: $(1-1/e-\varepsilon)$ with recourse $4\lceil 2/\varepsilon\rceil+2$ and polynomially many queries
-- statement:
--   Suppose the objective $f$ on the whole stream $V$ is a nonnegative weighted coverage function $f(S)=\sum_{a\in U}w_a\mathbf 1\{S\cap C_a\ne\emptyset\}$.
--
--   For every $\varepsilon\in(0,1-1/e)$ there are a randomized online algorithm and a polynomial bound $c\,(t+k+1)^d$ such that, for every such stream, every capacity $k\ge1$ and every arrival $t$:
--
--   1. on every outcome, arrival $t$ makes at most $c\,(|X_t|+k+1)^d$ current value queries, and the algorithm never accesses the features or weights;
--   2. on every outcome, $S_t\subseteq X_t$, $|S_t|\le k$ and
--   $$|S_t\triangle S_{t-1}|\le 4\lceil 2/\varepsilon\rceil+2;$$
--   3. $S_t$ is a random variable and, at every fixed time $t$,
--   $$\mathbb E f(S_t)\ \ge\ \Big(1-\frac1e-\varepsilon\Big)\mathrm{OPT}_k(X_t).$$
--
--   Coverage thus keeps the offline $1-1/e$ guarantee up to $\varepsilon$ under consistency, while general objectives fall to $2-\sqrt2$ (Theorem 1.1).
--
--   Differences from the source:
--   - encoding: a finite ground set V whose elements arrive one at a time; X_t the first t arrivals → V = Fin N with element i the (i+1)-st arrival, X_t = {0, …, t−1}, objectives read on sets of arrival indices (natFn), OPT_k(X_t) = optAt k F t; reason: the algorithm sees the objective only through its values, so naming elements by arrival index changes no instance
--   - encoding: a randomized algorithm using polynomially many current value queries per arrival (no claim about computation) → OnlineAlg: a seed space (Ω, μ) chosen with the algorithm, computation and sampling free, queries on subsets of X_t counted; per-arrival query count ≤ c(t + k + 1)^d with c, d depending only on the theorem's parameters; reason: the theorem bounds queries only; a polynomial in |X_t| and k is exactly a bound c(t+k+1)^d
--   - encoding: bounds for every outcome of the randomness; almost-sure termination after every arrival → query, capacity and recourse bounds (and termination within the budget) required for every seed; reason: worst case over seeds as on the page; requiring it on null sets too only restricts the algorithm
--   - encoding: E f(S_t), an expectation over the algorithm's randomness → the conclusion also asserts that {ω | S_t(ω) = S} is measurable for every S, and the expectation is the integral over the seed (tape) law; reason: makes the expectation genuine; it only adds to what the algorithm must satisfy
--   - encoding: integer capacity k ≥ 1 (p.1) → hypothesis 1 ≤ k; reason: the model's standing assumption
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §7, Theorem 7.1, p.21; §2.1, p.4; proof p.24

import Mathlib
import Definitions.Def_SharpConsist_Supplement_natFn
import Definitions.Def_SharpConsist_Supplement_optAt
import Definitions.Def_SharpConsist_Supplement_IsWeightedCoverage
import Definitions.Def_SharpConsist_Supplement_OnlineAlg

namespace SharpConsist.Supplement

/-- **Theorem 7.1 (coverage without its representation).** Fu–Zhang–Tao, *A Sharp Barrier of
Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §7,
Theorem 7.1, p.21; model §1, p.1 and §2.1, p.4.

For every `ε ∈ (0, 1 − 1/e)` there are a randomized online value-oracle algorithm (seed space
`(Ω, μ)`) and a polynomial bound `c (t + k + 1)^d` such that, on every stream `V = Fin N` whose
objective `f` is a nonnegative weighted coverage function on `V`, every capacity `k ≥ 1`, every
`t ≤ N` and every seed: arrival `t` makes at most `c (t + k + 1)^d` value queries, `|S_t| ≤ k` and
`|S_t △ S_{t−1}| ≤ 4⌈2/ε⌉ + 2`; and `S_t` is a random variable with
`E f(S_t) ≥ (1 − 1/e − ε) OPT_k(X_t)`.

**Formalization Note.** The algorithm sees only values of `f` (no side information: `sd = 0`), never
the features or weights. Computation and sampling are free; only queries are counted. -/
theorem theorem_7_1 :
    ∀ ε : ℝ, 0 < ε → ε < 1 - Real.exp (-1) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
        MeasureTheory.IsProbabilityMeasure μ ∧ ∃ (A : OnlineAlg Ω) (c d : ℕ),
        ∀ (N : ℕ) (f : Finset (Fin N) → ℝ), IsWeightedCoverage f →
        ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ N →
          (∀ ω : Ω, A.QueriesAtMost ω k (natFn f) (fun _ => 0) t (c * (t + k + 1) ^ d)) ∧
          (∀ ω : Ω, (A.out ω k (natFn f) (fun _ => 0) t).card ≤ k ∧
            (symmDiff (A.out ω k (natFn f) (fun _ => 0) t)
              (A.out ω k (natFn f) (fun _ => 0) (t - 1))).card ≤ 4 * ⌈2 / ε⌉₊ + 2) ∧
          (∀ S : Finset ℕ, MeasurableSet {ω | A.out ω k (natFn f) (fun _ => 0) t = S}) ∧
          (1 - Real.exp (-1) - ε) * optAt k (natFn f) t ≤
            ∫ ω, natFn f (A.out ω k (natFn f) (fun _ => 0) t) ∂μ := by sorry

end SharpConsist.Supplement
