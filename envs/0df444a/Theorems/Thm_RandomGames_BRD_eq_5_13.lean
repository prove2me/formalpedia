-- Prove2me | Theorems.Thm_RandomGames_BRD_eq_5_13
-- name    : RandomGames.BRD.eq_5_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:13.023185+00:00
-- url     : https://prove2.me/theorems/1d9bb8bd-36fc-426c-b7fa-7e82caef882c
-- title:
--   (5.13), proof of Theorem 2.4, p. 18 — summable lower tail of the number of pure Nash equilibria
-- statement:
--   Let $\alpha=\mathsf P(Z_1=Z_2)>0$ and let $\varepsilon>0$ satisfy $1+\varepsilon<(1+\alpha)^{1/2}$. Then
--   $$\sum_{N=1}^\infty \mathsf P\Bigl(\mathsf{card}(\mathsf{PNE}(\Xi_N)) < (1+\alpha)^N-(1+\varepsilon)^N(1+\alpha)^{N/2}\Bigr) < \infty. \tag{5.13}$$
--
--   The number of PNE falls below its mean by more than $(1+\varepsilon)^N$ standard deviations only with summable probability. The proof of Theorem 3.4 uses this to guarantee many PNE.
--
--   **Formalization Note** The page's "for any $\varepsilon>0$ small enough" is made precise by the next line of the page, "Fix $\varepsilon>0$ such that $(1+\varepsilon)<(1+\alpha)^{1/2}$", which is the hypothesis here; it is also the constraint on $\varepsilon$ in (5.32). Powers with exponent $N/2$ are real powers.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 18, (5.13), proof of Theorem 2.4

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory

/-- (5.13), proof of Theorem 2.4, p. 18: for `α > 0` and `ε > 0` with `1 + ε < (1 + α)^{1/2}`,
`∑_N P(card(PNE(Ξ_N)) < (1 + α)^N − (1 + ε)^N (1 + α)^{N/2}) < ∞`. -/
theorem eq_5_13 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hα : 0 < alpha μ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : 1 + ε < (1 + alpha μ) ^ ((1 : ℝ) / 2)) :
    ∑' N, gameMeasure μ N {Z | (pneCount Z : ℝ) <
      (1 + alpha μ) ^ N - (1 + ε) ^ N * (1 + alpha μ) ^ ((N : ℝ) / 2)} ≠ ⊤ := by sorry

end RandomGames.BRD
