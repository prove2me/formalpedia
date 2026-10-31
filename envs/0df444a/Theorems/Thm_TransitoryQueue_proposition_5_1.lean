-- Prove2me | Theorems.Thm_TransitoryQueue_proposition_5_1
-- name    : TransitoryQueue.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:00:25.754008+00:00
-- url     : https://prove2.me/theorems/d0b17737-e871-4d03-aba2-af4cd293fde8
-- title:
--   Proposition 5.1 — KMT for centred partial sums at every index, uniformly in $n$
-- statement:
--   Let $\rho$ be a law on $\mathbb R$ with a moment generating function finite near $0$, mean $\mu$ and standard deviation $\sigma$ ($\sigma=0$ allowed). There are constants $C_1,K_1,\lambda_1>0$ such that for every standard Brownian motion $B$ (on any probability space) and every $n\ge1$ there are iid $X_1,\dots,X_n$ with law $\rho$, each a measurable function of the path of $B$, with, for all $x>0$,
--
--   $$P\Bigl(\max_{0\le k\le n}\Bigl|\frac1{\sqrt n}\sum_{i=1}^{k}(X_i-\mu)-\sigma B_{k/n}\Bigr|>C_1\frac{\log n}{\sqrt n}+x\Bigr)<K_1e^{-\lambda_1x\sqrt n}.$$
--
--   In particular the printed bound holds for $\sup_{t\ge0}$ at $k=J_n(t)$, for any index process $J_n:[0,\infty)\to\{1,\dots,n\}$.
--
--   Differences from the source:
--   - generalization: "there exists a standard Brownian motion B and a version of X_1, …, X_n" → for every Brownian motion B given in advance there is a version X_1, …, X_n measurable with respect to B; reason: a statement for every B implies the printed existence; it is what lets one Brownian motion serve every n
--   - generalization: sup over t ∈ [0, ∞) at the index J_n(t) of an arbitrary process J_n with values in {1, …, n} → max over every k ∈ {0, …, n}; reason: the max over all k bounds the value at any J_n(t), so the printed bound follows for every J_n
--   - reading: constants C_1, K_1, λ_1 (dependence on n not stated) → constants chosen before n, the probability space and B; reason: the stronger reading; the proof's constants come from Theorem 3.1 and depend only on the law
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Proposition 5.1, p.24

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u

namespace TransitoryQueue

/-- **Proposition 5.1 (KMT at a random index).** Let `ρ` be a law on `ℝ` with a moment generating
function finite near `0`, mean `μ` and standard deviation `σ`. There are constants
`C_1, K_1, λ_1 > 0` such that for every standard Brownian motion `B` and every `n ≥ 1` there is an
iid sample `X_1, …, X_n` of law `ρ`, built from `B`, with, for all `x > 0`,
`P(max_{0≤k≤n} |n^{-1/2} Σ_{i=1}^{k} (X_i - μ) - σ B_{k/n}| > C_1 log n/√n + x) < K_1 e^{-λ_1 x √n}`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Proposition 5.1, p.24.

**Formalization Note** The printed bound is over `J_n(t)` for an arbitrary index process
`J_n : [0, ∞) → {1, …, n}`; it follows from the bound over every `k ≤ n` stated here. The printed
"there exists a standard Brownian motion B" is strengthened to every Brownian motion given in
advance, with `X_i` measurable with respect to the σ-algebra of `B`; the constants do not depend on
`n`. `σ = 0` is allowed. -/
theorem proposition_5_1 (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, |l| < δ → Integrable (fun y => Real.exp (l * y)) ρ) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ n : ℕ, 1 ≤ n →
        ∃ X : Fin n → Ω → ℝ, (∀ i, HasLaw (X i) ρ P) ∧ iIndepFun X P ∧
          (∀ i, Measurable[MeasurableSpace.comap (fun ω (s : ℝ≥0) => B s ω) inferInstance]
            (X i)) ∧
          ∀ x : ℝ, 0 < x →
            P.real {ω | ∃ k : ℕ, k ≤ n ∧ C * Real.log n / Real.sqrt n + x <
                |(∑ i : Fin n with i.val < k, (X i ω - ∫ y, y ∂ρ)) / Real.sqrt n
                  - Real.sqrt (variance id ρ) * B ((k : ℝ≥0) / (n : ℝ≥0)) ω|}
              < K * Real.exp (-(lam * x * Real.sqrt n)) := by sorry

end TransitoryQueue
