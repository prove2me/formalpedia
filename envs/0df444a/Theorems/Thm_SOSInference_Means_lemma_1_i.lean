-- Prove2me | Theorems.Thm_SOSInference_Means_lemma_1_i
-- name    : SOSInference.Means.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:39.117755+00:00
-- url     : https://prove2.me/theorems/cd47615f-4061-45f8-9017-ea9c54a4bd70
-- title:
--   Lemma 1 (first bound) — uniform $n^{-1/2}$ empirical-process bound for the indicators $I(T_i(n,\lambda)\le t)$
-- statement:
--   Assume A1)–A4) in dimension $l\ge1$, and fix a deterministic vector $\lambda\in\mathbb R^l$ and $T\in(0,\infty)$. Let $T_i(n,\lambda)$ be the first-arrival times of the $n$-sample. Then
--   $$\limsup_{n\to\infty}\ \mathbb E\Bigg(\sup_{t\in[0,T]}\Bigg|\frac1{n^{1/2}}\sum_{i=1}^n\Big(I\big(T_i(n,\lambda)\le t\big)-\mathbb P\big[T_i(n,\lambda)\le t\big]\Big)\Bigg|\Bigg)<\infty .$$
--
--   This is a rate of convergence for the Glivenko–Cantelli theorem associated with the dependent array $\{T_i(n,\lambda)\}_{i\le n}$; it lets the empirical averages in (27) be replaced by their expectations up to $O_p(n^{-1/2})$, uniformly over compact ranges of $t$.
--
--   **Formalization Note** The page prints $\overline{\lim}$, read as $\limsup$. The expectation of the nonnegative supremum is a lower Lebesgue integral with values in $[0,\infty]$, so finiteness is a genuine claim.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 40, Lemma 1 (first display)

import Mathlib
import Definitions.Def_SOSInference_Means_Tarr

namespace SOSInference.Means

open MeasureTheory

/-- **Lemma 1** (first display), p. 40 (Blanchet, Kang, Sample Out-of-Sample Inference Based on
Wasserstein Distance, arXiv:1605.01340v4, p. 40, Lemma 1): under A1)–A4), for a fixed
(deterministic) `λ ∈ ℝ^l` and any `T ∈ (0, ∞)`,
`limsup_{n→∞} E( sup_{t∈[0,T]} | n^{−1/2} Σ_{i=1}^n (I(T_i(n, λ) ≤ t) − P[T_i(n, λ) ≤ t]) | ) < ∞`.

**Formalization Note.** The page prints `lim` with an overline: `limsup`. The expectation of the
nonnegative supremum is a lower Lebesgue integral (`∫⁻`, values in `[0, ∞]`), so it is never a
default value. `T_i(n, λ)` is the first-arrival time `Tarr` computed from the `n`-sample
(`i < n` in Lean's indexing). `λ` here is a fixed vector, not the dual variable. -/
theorem lemma_1_i {l : ℕ} (hl : 1 ≤ l) (M : Model l) (hM : M.Standing) (lam : E l) (T : ℝ)
    (hT : 0 < T) :
    Filter.limsup (fun n : ℕ => ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          ((if Tarr M n i lam ω ≤ t then (1 : ℝ) else 0) -
            (M.P {ω' | Tarr M n i lam ω' ≤ t}).toReal)| ∂M.P)
      Filter.atTop < ⊤ := by sorry

end SOSInference.Means
