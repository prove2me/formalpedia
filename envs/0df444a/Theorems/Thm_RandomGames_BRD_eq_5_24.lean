-- Prove2me | Theorems.Thm_RandomGames_BRD_eq_5_24
-- name    : RandomGames.BRD.eq_5_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:01.841998+00:00
-- url     : https://prove2.me/theorems/7353ed77-31ea-47b5-8a09-8db64e169f12
-- title:
--   (5.24), proof of Theorem 3.4, p. 21 — summably in N, the oriented hypercube of the random game has no trap
-- statement:
--   Let $\alpha=\mathsf P(Z_1=Z_2)>0$ satisfy (3.8), $\lfloor -1/\log_2(1/2+\alpha/2)\rfloor\le 3$. Then
--   $$\sum_{N=1}^\infty \mathsf P\bigl(\exists \text{ a trap in } \vec{\mathscr H}^\beta_N\bigr) < \infty. \tag{5.24}$$
--
--   Here a trap is a set of at least two profiles that is strongly connected in the oriented hypercube and that no oriented path leaves. Together with the trap reduction this gives Theorem 3.4.
--
--   **Formalization Note** The hypotheses are those of Theorem 3.4. A trap is `IsTrap` of the definition `RandomGames.BRD.Game`, which requires at least two vertices, so a single PNE is not a trap.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 21, (5.24), proof of Theorem 3.4

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory

/-- (5.24), proof of Theorem 3.4, p. 21: under the hypotheses of Theorem 3.4,
`∑_N P(∃ a trap in H→^β_N) < ∞`. -/
theorem eq_5_24 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hα : 0 < alpha μ)
    (h38 : Int.floor (-1 / Real.logb 2 (1 / 2 + alpha μ / 2)) ≤ 3) :
    ∑' N, gameMeasure μ N {Z | ∃ T : Finset (Profile N), IsTrap Z T} ≠ ⊤ := by sorry

end RandomGames.BRD
