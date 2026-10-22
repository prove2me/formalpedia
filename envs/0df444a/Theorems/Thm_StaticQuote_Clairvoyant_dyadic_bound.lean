-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_dyadic_bound
-- name    : StaticQuote.Clairvoyant.dyadic_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:17.566983+00:00
-- url     : https://prove2.me/theorems/7f981cd8-e00f-48f7-a2f6-5aa68c9b9945
-- title:
--   p. 19, proof of Theorem 4 — E[γ_{1:2^kN}/2^kN] is non-decreasing in k and E[γ_{1:N}/N] ≤ its lim sup
-- statement:
--   Under the standing assumptions of the model, fix $N\ge1$ and set
--   $$a_k = \mathbb E\Big[\frac{\gamma_{1:2^kN}(\omega)}{2^kN}\Big], \qquad k = 0,1,2,\dots$$
--   Then:
--   1. the sequence $(a_k)_{k\ge0}$ is non-decreasing (its first step is $\mathbb E[\gamma_{1:2N}/2N]\ge\mathbb E[\gamma_{1:N}/N]$);
--   2. $\displaystyle \mathbb E\Big[\frac{\gamma_{1:N}(\omega)}{N}\Big] \le \limsup_{k\to\infty} a_k.$
--
--   Iterating the doubling inequality along the horizons $N, 2N, 4N, \dots$ gives a monotone sequence of expected clairvoyant costs per customer, which therefore dominates its first term in the limit.
--
--   **Formalization Note.** $N\ge1$, since the paper's $\mathbb N$ starts at $1$ and the ratios are $0/0$ at $N=0$. Expectations and the $\limsup$ are taken in $[0,\infty]$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4 (dyadic bound): for every `N`, the sequence
`a_k = E[γ_{1:2^k N}(ω)/(2^k N)]` is non-decreasing (its `k = 0` step is
`E[γ_{1:2N}/2N] ≥ E[γ_{1:N}/N]`), and `E[γ_{1:N}(ω)/N] ≤ lim sup_{k→∞} a_k`.

**Formalization Notes.** `N ≥ 1` (the paper's ℕ starts at 1; at `N = 0` the ratios are `0/0`).
Expectations are `lintegral`s and the lim sup is taken in `ℝ≥0∞`. -/
theorem dyadic_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) (hN : 1 ≤ N) :
    Monotone (fun k : ℕ => ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ) ∧
      ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ ≤
        limsup (fun k : ℕ => ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ)
          atTop := by sorry

end StaticQuote.Clairvoyant
