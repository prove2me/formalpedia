-- Prove2me | Theorems.Thm_SpectrumLB_theorem_5_7
-- name    : SpectrumLB.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:22.343277+00:00
-- url     : https://prove2.me/theorems/2e6410cf-d0c6-4091-bb5c-a4adcc532880
-- title:
--   Theorem 5.7 — $D_{\mathrm{tr}}(\overline\rho^{(n)}_a,\overline\rho^{(n)}_b)=o(1)$ for $n=o(d^{2-4/(k+4)})$
-- statement:
--   Let $k\ge2$ be even and let $a,b$ be sequences of $K$ positive integers with $\sum_ia_i^j=\sum_ib_i^j$ for $1\le j<k$. Then $D_{\mathrm{tr}}(\overline\rho^{(n)}_a,\overline\rho^{(n)}_b)=o(1)$ whenever $n=o(d^{2-4/(k+4)})$: for every $\varepsilon>0$ there are $\eta>0$ and $d_0$ such that for every $d\ge d_0$ divisible by each $a_i$ and $b_i$ and every $n\le\eta\,d^{2-4/(k+4)}$,
--
--   $$
--   D_{\mathrm{tr}}\big(\overline\rho^{(n)}_a,\overline\rho^{(n)}_b\big)\ \le\ \varepsilon ,
--   $$
--
--   where $\overline\rho^{(n)}_e$ is the average $n$-copy state of the tilted product-of-projections ensemble and $D_{\mathrm{tr}}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$. No measurement on fewer than $d^{2-4/(k+4)}$ copies can tell the two ensembles apart.
--
--   Differences from the source:
--   - generalization: a, b from Proposition 5.2 (K = 2^{k−1}) → any K and positive a, b with equal power sums for 1 ≤ j < k; reason: the proof uses only these properties (paper.md R5); Proposition 5.2's sequences satisfy them
--   - reading: k (§5) → k even and k ≥ 2; reason: §5's standing assumption ("we will only consider even k", p. 20)
--   - encoding: o(·) ⇒ o(1) → ∀ ε > 0, ∃ η > 0, ∃ d₀, ∀ d ≥ d₀, ∀ n ≤ η·d^{2−4/(k+4)}: D_tr ≤ ε; reason: uniform form, equivalent to the sequential statement (paper.md R4)
--   - encoding: d a multiple of each a_i, b_i → 0 < d, a_i ∣ d and b_i ∣ d for all i; reason: Definition 3.4's standing hypothesis
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 5.7, Eq. (5.10), p. 22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_SpectrumLB_avgState

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Theorem 5.7 (statistical indistinguishability).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Theorem 5.7, Eq. (5.10), p. 22: "For n = o(d^{2−4/(k+4)}), D_tr(ρ̄_a^{(n)}, ρ̄_b^{(n)}) = o(1)."

**Formalization Note.** `k` even, `≥ 2` (§5). `a, b` are any positive sequences of the same length whose
power sums agree for `1 ≤ j < k` (reading R5; the instance of Proposition 5.2 is one). `o(·) ⇒ o(1)` as in
reading R4; `d ≥ 1` divisible by every `a_i`, `b_i`. `D_tr` is the platform's `traceDistance`
(`½‖·‖₁`, Definition 2.3). -/
theorem theorem_5_7 (k : ℕ) (hk : Even k) (hk2 : 2 ≤ k) {K : ℕ} (a b : Fin K → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hpow : ∀ j : ℕ, 1 ≤ j → j < k → ∑ i, a i ^ j = ∑ i, b i ^ j) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
      (∀ i, a i ∣ d) → (∀ i, b i ∣ d) →
      ∀ n : ℕ, (n : ℝ) ≤ η * (d : ℝ) ^ ((2 : ℝ) - 4 / ((k : ℝ) + 4)) →
        QAlgorithms.traceDistance (avgState d n a) (avgState d n b) ≤ ε := by sorry

end SpectrumLB
