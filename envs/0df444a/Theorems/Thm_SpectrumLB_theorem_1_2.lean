-- Prove2me | Theorems.Thm_SpectrumLB_theorem_1_2
-- name    : SpectrumLB.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:34.602216+00:00
-- url     : https://prove2.me/theorems/4a2be8f7-6cf7-4bef-ac0a-c49a179ab57e
-- title:
--   Theorem 1.2 — spectrum estimation to constant precision needs $\Omega(d^{2-2/(k/2+2)})$ copies
-- statement:
--   For every even integer $k\ge2$ there is a precision $\epsilon_k>0$, independent of the dimension, and constants $c>0$, $d_0$ such that the following holds for every $d\ge d_0$ and every $n$. If a measurement on $n$ copies of an unknown $d$-dimensional state estimates its spectrum to precision $\epsilon_k$ (Definition 1.1: for **every** density matrix $\rho$, with probability at least $2/3$ the output $\widehat\alpha\in\mathbb C^d$ satisfies $d^{\downarrow}_{\mathrm{TV}}(\widehat\alpha,\mathrm{spec}\,\rho)\le\epsilon_k$), then
--
--   $$
--   n\ \ge\ c\,d^{\,2-\frac{2}{k/2+2}} .
--   $$
--
--   In other words, for every $\gamma>0$ there are $\epsilon>0$, $c>0$, $d_0$ such that every measurement estimating the spectrum to precision $\epsilon$ on all states of dimension $d\ge d_0$ uses $n\ge c\,d^{2-\gamma}$ copies: $d^{2-o(1)}$ copies are necessary for constant-precision spectrum estimation, almost matching the $O(d^2)$ cost of full tomography.
--
--   Differences from the source:
--   - reading: d↓TV(α̂, spec ρ) for α̂ ∈ ℂ^d, while Definition 2.1 defines d↓TV only between probability distributions → ½ min over permutations σ of Σ_i |α̂_σ(i) − λ↓_i(ρ)|; reason: paper.md R1; equals Definition 2.1 on probability vectors and is defined on every output, so the bound covers at least every algorithm the source covers
--   - encoding: an algorithm on n copies → a POVM on (ℂ^d)^⊗n with Borel outcomes in ℂ^d, success probability Re Tr(E(S) ρ^⊗n); reason: every algorithm with measurable post-processing is such a POVM
--   - encoding: copy complexity at least Ω(d^θ) with dimension-independent ε_k → ∃ ε > 0, ∃ c > 0, ∃ d₀, ∀ d ≥ d₀, ∀ n, ∀ E: success ⇒ c·d^θ ≤ n; reason: paper.md R2; ε is chosen before d
--   - reading: "at least d^{2−o(1)} copies are necessary for constant-precision spectrum estimation" → ∀ γ > 0, ∃ ε > 0, ∃ c > 0, ∃ d₀ with c·d^{2−γ} ≤ n; reason: the sentence restates the first clause over all k, whose precision ε_k depends on k
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 1.2, p. 3; Definition 1.1, p. 3

import Mathlib
import Definitions.Def_SpectrumLB_SpectrumEstimates

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Theorem 1.2 (spectrum estimation lower bound).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Theorem 1.2, p. 3: "For every even k ≥ 2, there exists a dimension-independent ϵ_k > 0 such that the
copy complexity of spectrum estimation with precision ϵ_k is at least Ω(d^{2−2/(k/2+2)}). In other words,
at least d^{2−o(1)} copies are necessary for constant-precision spectrum estimation of d-dimensional states."

(i) For every even `k ≥ 2` there are `ε > 0`, `c > 0`, `d₀` such that for all `d ≥ d₀`, all `n` and every POVM
`E` on `(ℂ^d)^{⊗n}` with outcomes in `ℂ^d` that estimates the spectrum of every state to precision `ε` with
probability `≥ 2/3`, `n ≥ c · d^{2 − 2/(k/2+2)}`. (ii) For every `γ > 0` the same holds with `d^{2−γ}`.

**Formalization Note.** `Ω(·)` is `∃ c > 0, ∃ d₀, ∀ d ≥ d₀` with `ε` chosen first ("dimension-independent",
reading R2). Every `d ≥ d₀` is covered, not only multiples of the hard instance's `a_i` (reading R3). The
exponent is a real power. Success is required on every density matrix (Definition 1.1). -/
theorem theorem_1_2 :
    (∀ k : ℕ, Even k → 2 ≤ k →
      ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ n : ℕ,
        ∀ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) (Fin d → ℂ),
          SpectrumEstimates d n ε E →
            c * (d : ℝ) ^ ((2 : ℝ) - 2 / ((k : ℝ) / 2 + 2)) ≤ n) ∧
    (∀ γ : ℝ, 0 < γ →
      ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ n : ℕ,
        ∀ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) (Fin d → ℂ),
          SpectrumEstimates d n ε E →
            c * (d : ℝ) ^ ((2 : ℝ) - γ) ≤ n) := by sorry

end SpectrumLB
