-- Prove2me | Theorems.Thm_SOSInference_Means_lemma_1_ii
-- name    : SOSInference.Means.lemma_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:46.561977+00:00
-- url     : https://prove2.me/theorems/323e0247-1935-4c3a-802d-70733bce372b
-- title:
--   Lemma 1 (second bound) — uniform $n^{-1/2}$ empirical-process bound for $\max(t^2-T_i(n,\lambda)^\alpha,0)$
-- statement:
--   Assume A1)–A4) in dimension $l\ge1$, and fix a deterministic vector $\lambda\in\mathbb R^l$, $T\in(0,\infty)$ and $\alpha\in(0,2]$. Then
--   $$\limsup_{n\to\infty}\ \mathbb E\Bigg(\sup_{t\in[0,T]}\Bigg|\frac1{n^{1/2}}\sum_{i=1}^n\Big(\max\big(t^2-T_i(n,\lambda)^\alpha,0\big)-\mathbb E\big[\max\big(t^2-T_i(n,\lambda)^\alpha,0\big)\big]\Big)\Bigg|\Bigg)<\infty .$$
--
--   This is the form in which the bound is used for the averages $\frac1n\sum_i\max(\|\lambda\|_2^2-T_i^{2/l}/n^{2/l},0)$ of (27).
--
--   **Formalization Note** $\limsup$ of a lower Lebesgue integral, as in the first bound; the inner expectation is of a variable with values in $[0,t^2]$.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 40, Lemma 1 (second display)

import Mathlib
import Definitions.Def_SOSInference_Means_Tarr

namespace SOSInference.Means

open MeasureTheory

/-- **Lemma 1** (second display), p. 40 (Blanchet, Kang, Sample Out-of-Sample Inference Based on
Wasserstein Distance, arXiv:1605.01340v4, p. 40, Lemma 1): under A1)–A4), for a fixed
(deterministic) `λ ∈ ℝ^l`, any `T ∈ (0, ∞)` and `α ∈ (0, 2]`,
`limsup_{n→∞} E( sup_{t∈[0,T]} | n^{−1/2} Σ_{i=1}^n (max(t² − T_i(n, λ)^α, 0)
  − E[max(t² − T_i(n, λ)^α, 0)]) | ) < ∞`.

**Formalization Note.** `limsup` of a lower Lebesgue integral (`∫⁻`), as in `lemma_1_i`. The inner
expectation `E[max(t² − T_i^α, 0)]` is a Bochner integral of a function with values in `[0, t²]`.
`T_i(n, λ) ≥ 0`, so `T_i^α` is the usual real power. -/
theorem lemma_1_ii {l : ℕ} (hl : 1 ≤ l) (M : Model l) (hM : M.Standing) (lam : E l) (T : ℝ)
    (hT : 0 < T) (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2) :
    Filter.limsup (fun n : ℕ => ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          (max (t ^ 2 - Tarr M n i lam ω ^ α) 0 -
            ∫ ω', max (t ^ 2 - Tarr M n i lam ω' ^ α) 0 ∂M.P)| ∂M.P)
      Filter.atTop < ⊤ := by sorry

end SOSInference.Means
