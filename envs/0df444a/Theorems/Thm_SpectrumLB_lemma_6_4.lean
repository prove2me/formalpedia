-- Prove2me | Theorems.Thm_SpectrumLB_lemma_6_4
-- name    : SpectrumLB.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:00.477178+00:00
-- url     : https://prove2.me/theorems/461d3c7d-87b4-4b1b-8e3a-083233f18aa3
-- title:
--   Lemma 6.4 — $\mathrm{Tr}(\overline\rho^{(n)}_e\mathcal P_{2t})\le C_{k,t}\,n^{t+1}/d^{2t}$ for $n\le c_kd^2$
-- statement:
--   Let $e=(e_1,\dots,e_K)$ be positive integers. There is a constant $c>0$ such that for every $t\ge1$ there is $C>0$ with
--
--   $$
--   \mathrm{Tr}\big(\overline\rho^{(n)}_e\,\mathcal P_{2t}\big)\ \le\ C\,\frac{n^{t+1}}{d^{2t}}
--   $$
--
--   for every $d\ge1$ divisible by each $e_i$ and every $n\le c\,d^2$. Even Jucys–Murphy moments are small under the average state; this bounds the top-order term $\beta_k\mathcal P_k$ of the log-likelihood expansion.
--
--   Differences from the source:
--   - generalization: e ∈ {a, b}, constants c_k and C_{k,t} → every sequence e of positive integers, constants depending on e (c) and on e and t (C); reason: the proof uses only Lemma 6.11 for e (paper.md R5); the paper's a, b are instances
--   - encoding: "for some constant c_k > 0" → c chosen before t, C after t; reason: c_k is indexed by k only (the proof gives c_k = 1/(4C₀²))
--   - encoding: d a multiple of each e_i → 0 < d and e_i ∣ d for all i; reason: Definition 3.4's standing hypothesis
--   - encoding: Tr(·) compared with a real number → real part of the trace; reason: the trace is real (paper.md R8)
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 6.4, Eq. (6.15), p. 24

import Mathlib
import Definitions.Def_SpectrumLB_avgState
import Definitions.Def_SpectrumLB_jmPowSum

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 6.4 (even Jucys–Murphy moments).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 6.4, Eq. (6.15), p. 24: "For fixed t ≥ 1 and e ∈ {a, b}, Tr(ρ̄_e^{(n)} 𝒫_{2t}) ≤
C_{k,t} n^{t+1}/d^{2t}, whenever n ≤ c_k d^2 for some constant c_k > 0."

**Formalization Note.** `c_k` depends only on `k` (here: on `e`) and is chosen before `t`; `C_{k,t}` after
`t`. Stated for every positive sequence `e` (reading R5), `d ≥ 1`, `e_i ∣ d`. Real part of the trace (R8). -/
theorem lemma_6_4 {K : ℕ} (e : Fin K → ℕ) (he : ∀ i, 0 < e i) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 1 ≤ t → ∃ C : ℝ, 0 < C ∧
      ∀ d n : ℕ, 0 < d → (∀ i, e i ∣ d) → (n : ℝ) ≤ c * (d : ℝ) ^ 2 →
        (avgState d n e * jmPowSum d n (2 * t)).trace.re ≤
          C * (n : ℝ) ^ (t + 1) / (d : ℝ) ^ (2 * t) := by sorry

end SpectrumLB
