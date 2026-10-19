-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_superadditive
-- name    : StaticQuote.Clairvoyant.superadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:04.380681+00:00
-- url     : https://prove2.me/theorems/22a2b86a-eceb-46d9-b6a9-d202b676c705
-- title:
--   p. 19, proof of Theorem 4 — γ_{1:2N}(ω) ≥ γ_{1:N}(ω) + γ_{N+1:2N}(ω)
-- statement:
--   For every sample path $\omega$ of inter-arrival and service times and every $N$, the perfectly-clairvoyant costs (12) satisfy
--   $$\gamma_{1:2N}(\omega) \ge \gamma_{1:N}(\omega) + \gamma_{N+1:2N}(\omega).$$
--
--   Splitting the first $2N$ customers into two halves and dropping the single constraint that links them can only lower the optimal cost. This superadditivity drives the doubling argument in the proof of Theorem 4.
--
--   **Formalization Note.** No probabilistic assumption is used. At $N=0$ all three values are $0$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 19, proof of Theorem 4 (superadditivity): for any sample path of inter-arrival and
service times, `γ_{1:2N}(ω) ≥ γ_{1:N}(ω) + γ_{N+1:2N}(ω)` for all `N`.

**Formalization Note.** Pathwise, no hypotheses. At `N = 0` all three values are infima of the
empty sum, i.e. `0`. -/
theorem superadditive {Ω : Type*} [MeasurableSpace Ω] (Q : Model Ω) (ω : Ω) (N : ℕ) :
    Q.gamma 1 N ω + Q.gamma (N + 1) (2 * N) ω ≤ Q.gamma 1 (2 * N) ω := by sorry

end StaticQuote.Clairvoyant
