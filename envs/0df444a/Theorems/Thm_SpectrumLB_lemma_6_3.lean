-- Prove2me | Theorems.Thm_SpectrumLB_lemma_6_3
-- name    : SpectrumLB.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:19.997719+00:00
-- url     : https://prove2.me/theorems/e047ab2e-835b-4592-9dd9-75591428d753
-- title:
--   Lemma 6.3 — $\mathrm{Tr}(\overline\rho^{(n)}_e(\mathcal P^\circ_m)^2)=o(1)$ for $n=o(d^{\vartheta_m})$
-- statement:
--   Fix $m\ge2$ and positive integers $e=(e_1,\dots,e_K)$, and set
--
--   $$
--   \vartheta_m=2-\frac{2}{\lfloor m/2\rfloor+2}.
--   $$
--
--   Then $\mathrm{Tr}\big(\overline\rho^{(n)}_e(\mathcal P^\circ_m)^2\big)=o(1)$ whenever $n=o(d^{\vartheta_m})$: for every $\varepsilon>0$ there are $\eta>0$ and $d_0$ such that for all $d\ge d_0$ divisible by each $e_i$ and all $n\le\eta\,d^{\vartheta_m}$,
--
--   $$
--   \mathrm{Tr}\big(\overline\rho^{(n)}_e\,(\mathcal P^\circ_m)^2\big)\ \le\ \varepsilon .
--   $$
--
--   The fluctuating parts of the low-order Jucys–Murphy power sums are negligible under the average state, so only the identity components of the log-likelihood expansion survive below $d^{\vartheta_m}$ copies.
--
--   Differences from the source:
--   - generalization: e ∈ {a, b} → every sequence e of positive integers; reason: the proof uses only Lemma 6.11 and the combinatorial Lemmas 6.6–6.7, valid for every positive e (paper.md R5); the paper's a, b are instances
--   - encoding: o(·) ⇒ o(1) → ∀ ε > 0, ∃ η > 0, ∃ d₀, ∀ d ≥ d₀, ∀ n ≤ η·d^{ϑ_m}: trace ≤ ε; reason: uniform form, equivalent to the sequential statement (paper.md R4)
--   - encoding: d a multiple of each e_i → 0 < d and e_i ∣ d for all i; reason: Definition 3.4's standing hypothesis
--   - encoding: the identity component η_m of 𝒫_m → A_{m,∅}/d^m read in the group algebra; reason: paper.md R7
--   - encoding: Tr(·) compared with a real number → real part of the trace; reason: the trace is real (paper.md R8)
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §6, p. 24, and Lemma 6.3, Eqs. (6.13)–(6.14), p. 24

import Mathlib
import Definitions.Def_SpectrumLB_avgState
import Definitions.Def_SpectrumLB_jmPowSumCirc

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 6.3 (low-order power sums are negligible).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §6, p. 24, and Lemma 6.3, Eqs. (6.13)–(6.14), p. 24: "For fixed m ≥ 2, set
ϑ_m := 2 − 2/(⌊m/2⌋ + 2). Then, for e ∈ {a, b}, Tr(ρ̄_e^{(n)} (𝒫°_m)^2) = o(1), whenever n = o(d^{ϑ_m})."

**Formalization Note.** `o(·) ⇒ o(1)` is encoded uniformly (reading R4): for every `ε > 0` there are `η > 0`
and `d₀` with the trace `≤ ε` for all `d ≥ d₀` and all `n ≤ η d^{ϑ_m}`; this is equivalent to the sequential
reading. Stated for every positive sequence `e` (reading R5), `d ≥ 1`, `e_i ∣ d`. `⌊m/2⌋` is natural-number
division. `𝒫°_m` removes the group-algebra identity component (reading R7). Real part of the trace (R8). -/
theorem lemma_6_3 (m : ℕ) (hm : 2 ≤ m) {K : ℕ} (e : Fin K → ℕ) (he : ∀ i, 0 < e i) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d → (∀ i, e i ∣ d) →
      ∀ n : ℕ, (n : ℝ) ≤ η * (d : ℝ) ^ ((2 : ℝ) - 2 / (((m / 2 : ℕ) : ℝ) + 2)) →
        (avgState d n e * jmPowSumCirc d n m ^ 2).trace.re ≤ ε := by sorry

end SpectrumLB
