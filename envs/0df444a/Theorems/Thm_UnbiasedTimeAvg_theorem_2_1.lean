-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_theorem_2_1
-- name    : UnbiasedTimeAvg.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:35.628998+00:00
-- url     : https://prove2.me/theorems/c317bdba-30ae-4400-9756-42157e002969
-- title:
--   Theorem 2.1 — $\mathbb E f(X_h)\to\mu$, with bias and mean-square-error bounds
-- statement:
--   Assume the standing model and Assumption A1 with rate $\nu$. Then $\mathbb E f(X_h)$ has a finite limit $\mu$ as $h\to\infty$, and:
--
--   1. for $h\ge0$, $$\big|\mathbb E f(X_h)-\mu\big|\le\sqrt{\nu(h)};\qquad(2.10)$$
--   2. for $h\ge0$ and $k>0$, $$\Big|\mathbb E\Big(\frac1k\sum_{i=h}^{h+k-1}f(X_i)\Big)-\mu\Big|\le\frac{\bar\nu(\lfloor h/2\rfloor)}{\sqrt k};\qquad(2.11)$$
--   3. for $h\ge0$ and $k>0$, $$\mathbb E\Big[\Big(\frac1k\sum_{i=h}^{h+k-1}f(X_i)-\mu\Big)^2\Big]\le\frac{26\,\bar\nu(0)^2}{k}.\qquad(2.12)$$
--
--   The limit $\mu$ is the quantity all estimators of the paper target; the theorem gives explicit bias and mean-square-error bounds for conventional time averages.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: (2.5) E((f(X_{i,m}) − f(X_i))²) ≤ ν(i) → lower Lebesgue integral of the square compared with ν(i) in [0, ∞]; reason: the same expectation whether or not the square is integrable; changes no instance
--   - encoding: X_{i,m} = G_{i+m}(X_0; U_{−m}, …, U_{i−1}) with i.i.d. U_i, i ∈ ℤ → `coupledChain g x₀ U i m` (the chain started from x₀ at integer time −m) inside the structure `ChainModel`; reason: the same random variables; `ChainModel` collects the standing assumptions of pp.2 and 4 (measurable g and f, i.i.d. noise on ℤ, f(X_i) square-integrable)
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Theorem 2.1, (2.10)–(2.12), p.6; proof Appendix C, pp.23–24

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_ChainModel
import Definitions.Def_UnbiasedTimeAvg_AssumptionA1
import Definitions.Def_UnbiasedTimeAvg_nuBar

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **Theorem 2.1 (bias and mean square error of time averages).** Kahalé,
arXiv:2209.09581v1, Theorem 2.1, p.6: "Suppose that Assumption A1 holds. Then `E(f(X_h))` has a
finite limit `µ` as `h` goes to infinity. For `h ≥ 0`, `|E(f(X_h)) − µ| ≤ √ν(h)` (2.10). For
`h ≥ 0` and `k > 0`, `|E((1/k) Σ_{i=h}^{h+k−1} f(X_i)) − µ| ≤ ν̄(⌊h/2⌋)/√k` (2.11), and
`E(((1/k) Σ_{i=h}^{h+k−1} f(X_i) − µ)²) ≤ 26(ν̄(0))²/k` (2.12)."

**Formalization Note.** Expectations are Bochner integrals of square-integrable variables (standing
assumption of `ChainModel`). `⌊h/2⌋` is `h / 2` in `ℕ`. (2.10) has the plain `ν(h)`. -/
theorem theorem_2_1
    {Ω F F' : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace F']
    {P : Measure Ω} [IsProbabilityMeasure P] {U : ℤ → Ω → F'} {g : F → F' → F} {f : F → ℝ}
    {x₀ : F} (hM : ChainModel P U g f x₀) {ν : ℕ → ℝ} (hA1 : AssumptionA1 P U g f x₀ ν) :
    ∃ μ : ℝ, Tendsto (fun h : ℕ => ∫ ω, f (coupledChain g x₀ U h 0 ω) ∂P) atTop (𝓝 μ) ∧
      (∀ h : ℕ, |∫ ω, f (coupledChain g x₀ U h 0 ω) ∂P - μ| ≤ Real.sqrt (ν h)) ∧
      (∀ h k : ℕ, 0 < k →
        |∫ ω, (1 / (k : ℝ)) * ∑ i ∈ Finset.Ico h (h + k), f (coupledChain g x₀ U i 0 ω) ∂P - μ|
          ≤ nuBar ν (h / 2) / Real.sqrt k) ∧
      (∀ h k : ℕ, 0 < k →
        ∫ ω, ((1 / (k : ℝ)) * ∑ i ∈ Finset.Ico h (h + k), f (coupledChain g x₀ U i 0 ω) - μ) ^ 2 ∂P
          ≤ 26 * (nuBar ν 0) ^ 2 / k) := by sorry

end UnbiasedTimeAvg
