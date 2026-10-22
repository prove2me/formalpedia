-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_eq_15
-- name    : StaticQuote.Clairvoyant.eq_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:22.77108+00:00
-- url     : https://prove2.me/theorems/a8e7b094-07e1-4c59-ab63-7f91bd53e9c4
-- title:
--   (15), p. 19 — E[γ_{1:N}/N] ≤ lim sup_M E[γ_{1:M}/M] for every N
-- statement:
--   Under the standing assumptions of the model, for every $N\ge1$,
--   $$\mathbb E\Big[\frac{\gamma_{1:N}(\omega)}{N}\Big] \le \limsup_{M\to\infty}\ \mathbb E\Big[\frac{\gamma_{1:M}(\omega)}{M}\Big].$$
--
--   The expected clairvoyant cost per customer over any finite horizon is bounded by its asymptotic value. Together with (14) this gives Theorem 4.
--
--   **Formalization Note.** $N\ge1$ (the paper's $\mathbb N$ starts at $1$). Expectations and the $\limsup$ are taken in $[0,\infty]$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, (15)

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, (15): `E[γ_{1:N}(ω)/N] ≤ lim sup_{M→∞} E[γ_{1:M}(ω)/M]` for all `N`.

**Formalization Notes.** `N ≥ 1` (the paper's ℕ starts at 1). Expectations are `lintegral`s and
the lim sup is taken in `ℝ≥0∞`. -/
theorem eq_15 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) (hN : 1 ≤ N) :
    ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ ≤
      limsup (fun M : ℕ => ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ) atTop := by sorry

end StaticQuote.Clairvoyant
