-- Prove2me | Theorems.Thm_RandomGames_BRD_theorem_2_3
-- name    : RandomGames.BRD.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:02.433695+00:00
-- url     : https://prove2.me/theorems/1467a1e9-2a41-4352-b704-6065d8708a09
-- title:
--   Theorem 2.3, p. 7 — CLT for the number of pure Nash equilibria, with Kolmogorov-distance rate K_α N max((1 + α)/2, (1 + α)^{−1/2})^N
-- statement:
--   Assume the payoff law has atoms, i.e. $\alpha=\mathsf P(Z_1=Z_2)>0$, and let $\Phi$ be the standard normal distribution function. Then there is a constant $K_\alpha>0$, depending only on $\alpha$, such that for every $N\ge1$
--   $$\sup_{x}\left|\mathsf P\left(\frac{\mathsf{card}(\mathsf{PNE}(\Xi_N))-(1+\alpha)^N}{(1+\alpha)^{N/2}}\le x\right)-\Phi(x)\right| \le K_\alpha N\max\left(\frac{1+\alpha}{2},\frac{1}{(1+\alpha)^{1/2}}\right)^N. \tag{2.9}$$
--
--   Thus the number of PNE, centred at its mean $(1+\alpha)^N$ and scaled by $(1+\alpha)^{N/2}$, is asymptotically standard normal with an explicit geometric rate. In particular it grows exponentially in $N$ whenever $\alpha>0$.
--
--   **Formalization Note** $N\ge1$ is added (at $N=0$ there is exactly one PNE and the bound fails). "Depends only on $\alpha$" is $\forall\alpha>0\,\exists K>0\,\forall\mu$ with $\alpha(\mu)=\alpha$. The supremum over $x$ is written as a bound for every $x$. $(1+\alpha)^{N/2}$ and $(1+\alpha)^{1/2}$ are real powers. The paper's proof goes through (5.8), whose derivation in the paper is flawed; the statement is true and posed as printed.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 7, Theorem 2.3, (2.9)

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory ProbabilityTheory

/-- Theorem 2.3, p. 7 (CLT for pure Nash equilibria): for `α > 0` there is `K_α > 0`, depending
only on `α`, such that for all `N ≥ 1` and all `x`,
`|P((card(PNE(Ξ_N)) − (1+α)^N)/(1+α)^{N/2} ≤ x) − Φ(x)| ≤ K_α N max((1+α)/2, 1/(1+α)^{1/2})^N`. -/
theorem theorem_2_3 (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure ℝ, IsProbabilityMeasure μ → alpha μ = α →
      ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ,
        |((gameMeasure μ N) {Z | ((pneCount Z : ℝ) - (1 + α) ^ N) / (1 + α) ^ ((N : ℝ) / 2) ≤ x}).toReal
            - cdf (gaussianReal 0 1) x| ≤
          K * N * max ((1 + α) / 2) (1 / (1 + α) ^ ((1 : ℝ) / 2)) ^ N := by sorry

end RandomGames.BRD
