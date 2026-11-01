-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_13
-- name    : ProcessingNetworks.EntropyIneq.lemma_B_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:28.21504+00:00
-- url     : https://prove2.me/theorems/7d41e789-26b3-4856-a4d5-3425b8c6cfdd
-- title:
--   Lemma B.13 — relative-entropy lower bound for the traffic equations (corrected: $P$ substochastic)
-- statement:
--   Throughout, $I\ge1$ is an integer, $\mathcal I=\{1,\dots,I\}$ is the set of classes, $\lambda\in\mathbb R^I_+$ is the vector of external arrival rates and $P$ is a non-negative $I\times I$ routing matrix with spectral radius $\rho(P)<1$; $P_{i0}:=1-\sum_{j\in\mathcal I}P_{ij}$, $\mathcal I_+=\mathcal I\cup\{0\}$, $\alpha:=(I-P')^{-1}\lambda$ is assumed positive and $\alpha_0:=1$ (Section B.4, (B.13)–(B.17)). In addition, $P$ is **substochastic**: $\sum_{j\in\mathcal I}P_{ij}\le1$ for every $i$, i.e. $P_{i0}\ge0$.
--
--   Given $d\in\mathbb R^I$, define
--
--   $$
--   a:=\lambda+P'd\qquad\text{and}\qquad d_0=1 ,
--   $$
--
--   so $a_i=\lambda_i+\sum_jP_{ji}d_j$. Assume that $d_i>0$ for every $i\in\mathcal I$. Then
--
--   $$
--   \sum_{i\in\mathcal I}(d_i-a_i)\log\frac{d_i}{\alpha_i}\ \ge\ \frac12\,\frac1{\sum_{i\in\mathcal I}d_i+\sum_{i\in\mathcal I}\lambda_i}\Big(\sum_{i\in\mathcal I}\lambda_i\Big|1-\frac{d_i}{\alpha_i}\Big|+\sum_{i\in\mathcal I}\alpha_i\Big|\frac{d_i}{\alpha_i}-\sum_{j\in\mathcal I_+}P_{ij}\frac{d_j}{\alpha_j}\Big|\Big)^2 ,
--   $$
--
--   with $d_0=\alpha_0=1$.
--
--   With $d=\dot D(t)$ one has $d-a=-\dot Z(t)$, so the left side is minus the bound on the drift of the entropy Lyapunov function (Lemma 10.9) used in Section 10.5 to prove stability of the proportionally fair fluid model; the right side is non-negative and vanishes only when $d=\alpha$, which turns the inequality into a strict decrease away from the fixed point.
--
--   **Formalization Note** The sum over $\mathcal I_+$ is the sum over the classes plus the class-$0$ term $P_{i0}$; $\log$ is the natural logarithm, applied only to positive arguments.
--
--   Differences from the source:
--
--   - correction: P a non-negative I × I matrix with spectral radius < 1 (the section's printed hypothesis) → additionally every row sum of P is ≤ 1 (hypothesis hsub, P_{i0} ≥ 0); reason: the printed statement is false: P = [[0, 2], [0, 0]] (non-negative, ρ(P) = 0), λ = (1, 0), so α = (1, 2) > 0, and d = (0.1, 0.05) give left side 0.9 ln 10 + 0.15 ln 40 ≈ 2.626 < right side 3.9²/2.3 ≈ 6.613 (proved in Lean in the mission's verification file); the Guide (p.xv) defines spectral radius and transience for substochastic matrices only, and the proof's Jensen step (B.30) uses (P_ij)_{j∈𝓘₊} as probability weights
--   - encoding: sums over 𝓘₊ = 𝓘 ∪ {0} with d₀ = α₀ = 1 → a sum over Fin I plus the explicit class-0 term outflow P i = P_{i0}; reason: class 0 is not an element of Fin I; same values
--   - encoding: ρ(P) < 1, ρ the largest modulus of an eigenvalue → RobustToDynamics.specRadius P < 1, the supremum of the moduli of the points of the spectrum of P over ℂ; reason: that spectrum is the set of complex eigenvalues, a finite nonempty set for I ≥ 1, so the supremum is the maximum
--   - encoding: α := (I − P′)⁻¹λ → traffic lam P, defined with Matrix.inv; reason: ρ(P) < 1 makes I − P′ invertible (Theorem F.1), so Matrix.inv is the true inverse
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Lemma B.13, eqs. (B.27)–(B.28), p.271 (PDF 287)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions
import Definitions.Def_ProcessingNetworks_EntropyIneq_outflow

open Matrix

namespace ProcessingNetworks.EntropyIneq

/-- **Lemma B.13** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix B §B.4, Lemma B.13, eqs. (B.27)–(B.28), p.271 (PDF 287)), with `P`
substochastic. Let `λ` and `P` be as specified at the beginning of Section B.4 and `α = (I − P′)⁻¹λ`.
Given `d ∈ ℝ^I`, define `a := λ + P′d` and `d₀ = 1`. Assume that `dᵢ > 0` for `i ∈ 𝓘`. Then
`Σ_{i∈𝓘} (dᵢ − aᵢ) log(dᵢ/αᵢ) ≥ ½ · (Σ_{i∈𝓘} dᵢ + Σ_{i∈𝓘} λᵢ)⁻¹ ·
  (Σ_{i∈𝓘} λᵢ |1 − dᵢ/αᵢ| + Σ_{i∈𝓘} αᵢ |dᵢ/αᵢ − Σ_{j∈𝓘₊} P_{ij} d_j/α_j|)²`.

**Correction** The hypothesis `hsub` (every row sum of `P` is `≤ 1`, i.e. `P_{i0} ≥ 0`) is added to
the section's printed assumptions (non-negative `P` with spectral radius `< 1`). Without it the
lemma is false: `P = [[0, 2], [0, 0]]`, `λ = (1, 0)` (so `α = (1, 2) > 0`) and `d = (0.1, 0.05)`
give left side `≈ 2.626` and right side `≈ 6.613`. The book's Guide (p.xv) defines spectral
radius and "transient" for substochastic matrices only, and the proof's Jensen step (B.30) uses
`(P_{ij})_{j∈𝓘₊}` as probability weights.

**Formalization Note** `P′d` is `Pᵀ *ᵥ d`, so `aᵢ = λᵢ + Σ_j P_{ji} d_j`. `𝓘₊ = 𝓘 ∪ {0}`: the
inner sum is `Σ_{j ∈ Fin I} P_{ij} d_j/α_j + outflow P i` (`d₀ = α₀ = 1`). `log` is `Real.log`;
every argument `dᵢ/αᵢ` is positive. The prefactor is positive because `d > 0` and `I ≥ 1`. -/
theorem lemma_B_13 {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hB4 : SectionB4Assumptions lam P) (hsub : ∀ i, ∑ j, P i j ≤ 1)
    (d : Fin I → ℝ) (hd : ∀ i, 0 < d i) :
    let α := traffic lam P
    let a := lam + Pᵀ *ᵥ d
    (1 / 2 : ℝ) * (1 / (∑ i, d i + ∑ i, lam i)) *
        (∑ i, lam i * |1 - d i / α i| +
          ∑ i, α i * |d i / α i - (∑ j, P i j * (d j / α j) + outflow P i)|) ^ 2 ≤
      ∑ i, (d i - a i) * Real.log (d i / α i) := by sorry

end ProcessingNetworks.EntropyIneq
