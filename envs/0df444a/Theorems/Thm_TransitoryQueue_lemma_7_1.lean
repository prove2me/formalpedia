-- Prove2me | Theorems.Thm_TransitoryQueue_lemma_7_1
-- name    : TransitoryQueue.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:38.460983+00:00
-- url     : https://prove2.me/theorems/ef12a6c3-7efa-4c55-b9f8-1c0a54fc2f06
-- title:
--   Lemma 7.1 (corrected: $t\le S_n/c_n$) — strong embedding of the truncated renewal process
-- statement:
--   Let $\nu$ be a law on $[0,\infty)$ with a moment generating function finite near $0$, mean $\mu>0$ and standard deviation $\sigma$. Let $V_{n,1},\dots,V_{n,n}$ be iid with law $\nu$ and $B$ a Brownian motion satisfying the coupling (98) with constants $C,K,\lambda$. Then there are constants $C_{10},K_{10},\lambda_{10}>0$ such that for every efficiency $c>0$, every $n\ge1$ and every $x>0$, with $S_n=V_1+\dots+V_n$ and
--
--   $$Z_n(t)=c\Bigl(\frac t\mu-\frac{M_n(t)}{c}\Bigr),$$
--
--   $$P\Bigl(\sup_{0\le t\le S_n/c}\Bigl|\frac{Z_n(t)}{\sqrt n}-\frac\sigma\mu B_{M_n(t)/n}\Bigr|>C_{10}\frac{\log n}{\sqrt n}+x\Bigr)<K_{10}e^{-\lambda_{10}x\sqrt n}.$$
--
--   Differences from the source:
--   - correction: sup over t ∈ [0, ∞) in (111) → sup over 0 ≤ t ≤ S_n/c; reason: (111) is false: for t ≥ S_n/c_n, M_n(t) = n and Z_n(t) = c_n t/μ − n → ∞ while B_{M_n(t)/n} = B_1, so the supremum is +∞ almost surely; the range t ≤ S_n/c_n is where the paper uses the bound ((112), (120))
--   - reading: constants C_10, K_10, λ_10 (dependence on n and c_n not stated) → constants chosen before c and n; reason: the stronger reading; Theorem 2.11 uses the lemma for an arbitrary sequence c_n
--   - encoding: the version of V_1, …, V_n and B from (98) (Proposition 5.1) → hypotheses: laws, independence, B Brownian, and (98) at every index k ≤ n with constants C, K, λ; reason: this is the paper's standing coupling, stated as a hypothesis
--   - encoding: P(sup … > a) → P of the event that some t ∈ [0, S_n/c] exceeds a; reason: the same event
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Lemma 7.1, eq. (111), p.35

import Mathlib
import Definitions.Def_TransitoryQueue_completed
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- **Lemma 7.1, corrected (strong embedding of the truncated renewal process).** Let the service
times `V_1, …, V_n` be iid with law `ν` on `[0, ∞)` (finite moment generating function near `0`,
mean `μ > 0`, standard deviation `σ`) and coupled to a Brownian motion `B` as in (98) with
constants `C, K, λ`. Then there are constants `C_10, K_10, λ_10 > 0`, not depending on the
efficiency `c`, such that for all `c > 0`, `n ≥ 1`, `x > 0`, with `Z_n(t) = c (t/μ - M_n(t)/c)`
and `S_n = V_1 + ⋯ + V_n`:
`P(sup_{0 ≤ t ≤ S_n/c} |Z_n(t)/√n - (σ/μ) B_{M_n(t)/n}| > C_10 log n/√n + x) < K_10 e^{-λ_10 x √n}`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Lemma 7.1, p.35, eq. (111), corrected.

**Formalization Note** The printed supremum is over `t ∈ [0, ∞)`; it is `+∞` almost surely, since
for `t ≥ S_n/c`, `M_n(t) = n` and `Z_n(t) = c t/μ - n → ∞`. The range `t ≤ S_n/c` is where the
paper uses it ((120), (112)). The paper's coupling hypothesis is (98), here written for every
index `k ≤ n`. -/
theorem lemma_7_1 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, |l| < δ → Integrable (fun y => Real.exp (l * y)) ν)
    (hμ : 0 < ∫ y, y ∂ν)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : (n : ℕ) → Fin n → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hV_law : ∀ n i, HasLaw (V n i) ν P) (hV_indep : ∀ n, iIndepFun (V n) P)
    (C K lam : ℝ)
    (h98 : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
      P.real {ω | ∃ k : ℕ, k ≤ n ∧ C * Real.log n / Real.sqrt n + x <
          |(∑ i : Fin n with i.val < k, (V n i ω - ∫ y, y ∂ν)) / Real.sqrt n
            - Real.sqrt (variance id ν) * B ((k : ℝ≥0) / (n : ℝ≥0)) ω|}
        < K * Real.exp (-(lam * x * Real.sqrt n))) :
    ∃ C₁₀ K₁₀ lam₁₀ : ℝ, 0 < C₁₀ ∧ 0 < K₁₀ ∧ 0 < lam₁₀ ∧
      ∀ c : ℝ, 0 < c → ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
        P.real {ω | ∃ t : ℝ, 0 ≤ t ∧ t ≤ (∑ i : Fin n, V n i ω) / c ∧
            C₁₀ * Real.log n / Real.sqrt n + x <
              |c * (t / (∫ y, y ∂ν) - (completed c (fun i => V n i ω) t : ℝ) / c) / Real.sqrt n
                - Real.sqrt (variance id ν) / (∫ y, y ∂ν)
                  * B (((completed c (fun i => V n i ω) t : ℝ) / n).toNNReal) ω|}
          < K₁₀ * Real.exp (-(lam₁₀ * x * Real.sqrt n)) := by sorry

end TransitoryQueue
