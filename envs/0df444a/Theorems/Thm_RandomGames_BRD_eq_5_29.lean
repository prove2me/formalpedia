-- Prove2me | Theorems.Thm_RandomGames_BRD_eq_5_29
-- name    : RandomGames.BRD.eq_5_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:04.866075+00:00
-- url     : https://prove2.me/theorems/23334d32-9aba-4de1-b1ca-950a667a565d
-- title:
--   (5.29), proof of Theorem 3.4, p. 23 — summably in N, some pure Nash equilibrium is accessible from 0
-- statement:
--   Let $\alpha=\mathsf P(Z_1=Z_2)>0$ satisfy (3.8), $\lfloor -1/\log_2(1/2+\alpha/2)\rfloor\le 3$. Then
--   $$\sum_{N=1}^\infty \mathsf P\bigl(\vec{\mathscr L}^{\beta,\mathbf 0}_N \text{ contains no PNE}\bigr) < \infty, \tag{5.29}$$
--   where $\vec{\mathscr L}^{\beta,\mathbf 0}_N$ is the set of profiles accessible from $\mathbf 0$.
--
--   Since a trap contains no PNE, this rules out a trap that contains $\mathbf 0$'s whole accessible set, case (ii) of the proof of Theorem 3.4.
--
--   **Formalization Note** The hypotheses are those of Theorem 3.4, as in the paper's proof.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 23, (5.29), proof of Theorem 3.4

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory

/-- (5.29), proof of Theorem 3.4, p. 23: under the hypotheses of Theorem 3.4,
`∑_N P(L→^{β,0}_N contains no PNE) < ∞`. -/
theorem eq_5_29 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hα : 0 < alpha μ)
    (h38 : Int.floor (-1 / Real.logb 2 (1 / 2 + alpha μ / 2)) ≤ 3) :
    ∑' N, gameMeasure μ N {Z | ∀ s ∈ reach0 Z, ¬ IsPNE Z s} ≠ ⊤ := by sorry

end RandomGames.BRD
