-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_block_stationary
-- name    : StaticQuote.Clairvoyant.block_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:11.485444+00:00
-- url     : https://prove2.me/theorems/adf53ba5-7298-407e-a328-db111794b10d
-- title:
--   p. 19, proof of Theorem 4 — E[γ_{1:N}] = E[γ_{N+1:2N}]
-- statement:
--   Under the standing assumptions of the model (independent, identically distributed inter-arrival times and service times, all mutually independent), for every $N$,
--   $$\mathbb E[\gamma_{1:N}(\omega)] = \mathbb E[\gamma_{N+1:2N}(\omega)].$$
--
--   The clairvoyant cost of a block of $N$ consecutive customers depends only on the gaps between their arrival times and on their service times, and these have the same joint law for customers $1,\dots,N$ as for customers $N+1,\dots,2N$. This is the step of the proof of Theorem 4 where the i.i.d. assumptions are used.
--
--   **Formalization Note.** Expectations are lower Lebesgue integrals with values in $[0,\infty]$. The statement is false without the independence and identical-distribution hypotheses.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4 (block stationarity): `E[γ_{1:N}(ω)] = E[γ_{N+1:2N}(ω)]`
for all `N`.

**Formalization Note.** Expectations are `lintegral`s in `ℝ≥0∞`. The i.i.d. and mutual-independence
hypotheses in `Standing` are what make this true; it fails without them. -/
theorem block_stationary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) :
    ∫⁻ ω, Q.gamma 1 N ω ∂μ = ∫⁻ ω, Q.gamma (N + 1) (2 * N) ω ∂μ := by sorry

end StaticQuote.Clairvoyant
