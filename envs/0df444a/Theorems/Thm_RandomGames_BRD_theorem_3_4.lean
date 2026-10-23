-- Prove2me | Theorems.Thm_RandomGames_BRD_theorem_3_4
-- name    : RandomGames.BRD.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:15.856013+00:00
-- url     : https://prove2.me/theorems/7fab018c-d6e9-4e37-97c7-d661d06a3484
-- title:
--   Theorem 3.4, p. 10 — if α > 0 and ⌊−1/log₂(1/2 + α/2)⌋ ≤ 3, best-response dynamics from 0 fails to reach a pure Nash equilibrium with summable probability
-- statement:
--   Consider the random games $\Xi_N$ with i.i.d. payoffs of law $\mu$, let $\alpha=\mathsf P(Z_1=Z_2)$, and let $\mathsf{BR}^{(N)}$ be best-response dynamics started at $\mathbf 0$. If $\alpha>0$ satisfies
--   $$\left\lfloor -\frac{1}{\log_2(1/2+\alpha/2)}\right\rfloor \le 3, \tag{3.8}$$
--   i.e. if $0<\alpha<2^{3/4}-1\approx 0.68$, then
--   $$\sum_{N=1}^\infty \mathsf P\bigl(\mathsf{BR}^{(N)}\text{ does not converge to a PNE}\bigr) < \infty. \tag{3.9}$$
--
--   By the first Borel–Cantelli lemma, there is then a finite random $N^*$ such that best-response dynamics converges to a pure Nash equilibrium in every game $\Xi_N$ with $N\ge N^*$; random games with moderately many payoff ties are, for large $N$, solved by the simplest learning dynamics.
--
--   **Formalization Note** (3.8) is the hypothesis, verbatim, with `Int.floor`; the "i.e." clause is not added. The probability in (3.9) is the lower Lebesgue integral of the conditional non-convergence probability `notConvProb` against `gameMeasure μ N`; the chain stays put at a PNE, which the page leaves undefined. At $\alpha=1$ one has $\log_2 1=0$ and Lean's $-1/0=0$, so (3.8) holds by a junk value; the theorem is nevertheless true there, since every profile is then a PNE and the chain converges at once.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 10, Theorem 3.4, (3.8)–(3.9)

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory

/-- Theorem 3.4, p. 10: if `α > 0` satisfies (3.8), `⌊−1/log₂(1/2 + α/2)⌋ ≤ 3`, then (3.9):
`∑_N P(BR^(N) does not converge to a PNE) < ∞`. -/
theorem theorem_3_4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hα : 0 < alpha μ)
    (h38 : Int.floor (-1 / Real.logb 2 (1 / 2 + alpha μ / 2)) ≤ 3) :
    ∑' N, ∫⁻ Z, notConvProb Z ∂(gameMeasure μ N) ≠ ⊤ := by sorry

end RandomGames.BRD
