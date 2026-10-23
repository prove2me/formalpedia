-- Prove2me | Theorems.Thm_RandomGames_BRD_eq_5_8
-- name    : RandomGames.BRD.eq_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:03.073653+00:00
-- url     : https://prove2.me/theorems/335c8339-05a7-43e1-b09a-44e582e46c76
-- title:
--   (5.8), proof of Theorem 2.3, p. 18 — total-variation Poisson approximation of the number of pure Nash equilibria
-- statement:
--   Let $\alpha>0$. There is a constant $K_{1,\alpha}$, depending on $\alpha$ but not on $N$ (nor on the payoff law beyond $\alpha$), such that for every payoff law $\mu$ with $\mathsf P(Z_1=Z_2)=\alpha$ and every $N\ge1$,
--   $$\rho_{\mathsf{TV}}\Bigl(\mathsf{card}(\mathsf{PNE}(\Xi_N)),\ \mathsf{Poisson}\bigl(2^N(1-\beta)^N\bigr)\Bigr) \le K_{1,\alpha}\bigl(N(1-\beta)^N\bigr), \tag{5.8}$$
--   where $\beta=(1-\alpha)/2$ and $\rho_{\mathsf{TV}}(P,Q)=\sup_{A\subseteq\mathbb N}|P(A)-Q(A)|$ is the total variation distance (5.5) between the law of the number of PNE and the Poisson law.
--
--   Since $\mathsf E[\mathsf{card}(\mathsf{PNE}(\Xi_N))]=2^N(1-\beta)^N$, this says the number of PNE is close to Poisson with the same mean, with an error that decays geometrically in $N$.
--
--   **Formalization Note** $N\ge1$ is added: at $N=0$ the right side is $0$ while the left side is $\rho_{\mathsf{TV}}(\delta_1,\mathsf{Poisson}(1))>0$. "Depends on $\alpha$, but not on $N$" is rendered as $\forall\alpha\,\exists K\,\forall\mu$ with $\alpha(\mu)=\alpha$, $\forall N\ge1$; the law of the orientation depends on $\mu$ only through $\alpha$. $\rho_{\mathsf{TV}}$ is the published `MarkovChainCLT.tvDist` on $\mathbb N$ with its discrete $\sigma$-algebra. The paper derives (5.8) from an identity in law between the PNE count and the isolated vertices of the percolation that is false (the two laws differ already at $N=2$); the statement itself is true by the Chen–Stein method and is posed as printed.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 18, (5.8), proof of Theorem 2.3; ρ_TV as in (5.5), p. 17

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

open MeasureTheory ProbabilityTheory

/-- (5.8), proof of Theorem 2.3, p. 18: for `α > 0` there is a constant `K_{1,α}`, depending on
`α` but not on `N`, with
`ρ_TV(card(PNE(Ξ_N)), Poisson(2^N(1 − β)^N)) ≤ K_{1,α} N(1 − β)^N` for all `N ≥ 1`. -/
theorem eq_5_8 (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, ∀ μ : Measure ℝ, IsProbabilityMeasure μ → alpha μ = α →
      ∀ N : ℕ, 1 ≤ N →
        MarkovChainCLT.tvDist ((gameMeasure μ N).map (fun Z => pneCount Z))
          (poissonMeasure (Real.toNNReal (2 ^ N * (1 - beta μ) ^ N))) ≤
          K * (N * (1 - beta μ) ^ N) := by sorry

end RandomGames.BRD
