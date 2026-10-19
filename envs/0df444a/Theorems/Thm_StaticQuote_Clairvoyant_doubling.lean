-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_doubling
-- name    : StaticQuote.Clairvoyant.doubling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:17.152728+00:00
-- url     : https://prove2.me/theorems/81116373-0817-486a-9635-bea0a89c9b12
-- title:
--   p. 19, proof of Theorem 4 — E[γ_{1:2N}] ≥ 2 E[γ_{1:N}]
-- statement:
--   Under the standing assumptions of the model, for every $N$,
--   $$\mathbb E[\gamma_{1:2N}(\omega)] \ge 2\,\mathbb E[\gamma_{1:N}(\omega)].$$
--
--   It follows from superadditivity of the clairvoyant cost and the equality of the expected costs of the two halves. It shows that the expected clairvoyant cost per customer does not decrease when the horizon is doubled.
--
--   **Formalization Note.** Expectations are lower Lebesgue integrals with values in $[0,\infty]$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4 (doubling): `E[γ_{1:2N}(ω)] ≥ 2 E[γ_{1:N}(ω)]` for all `N`.

**Formalization Note.** Expectations are `lintegral`s in `ℝ≥0∞`. -/
theorem doubling {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) :
    2 * ∫⁻ ω, Q.gamma 1 N ω ∂μ ≤ ∫⁻ ω, Q.gamma 1 (2 * N) ω ∂μ := by sorry

end StaticQuote.Clairvoyant
