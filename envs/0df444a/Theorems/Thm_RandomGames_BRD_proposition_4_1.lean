-- Prove2me | Theorems.Thm_RandomGames_BRD_proposition_4_1
-- name    : RandomGames.BRD.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:59.37799+00:00
-- url     : https://prove2.me/theorems/a1792b04-3d3a-4877-9758-0c0e955c220a
-- title:
--   Proposition 4.1, p. 12 — coupling of the accessible set L→^{β,0}_N with the open cluster of 0 in a percolation B^β_N
-- statement:
--   Let $\Xi_N$ be the random game whose payoffs are i.i.d. with law $\mu$, and let $\beta=\mathsf P(Z_1<Z_2)\in[0,1/2]$. Then there is a bond percolation $\mathscr B^\beta_N$ on the hypercube $\mathscr H_N$ with parameter $\beta$, defined on the same probability space as $\Xi_N$ enlarged by an independent auxiliary percolation, such that the vertex set of its open cluster containing $\mathbf 0$ coincides with the set of profiles accessible from $\mathbf 0$:
--   $$\mathscr L^{\beta,\mathbf 0}_N = \vec{\mathscr L}^{\beta,\mathbf 0}_N .$$
--
--   This coupling transfers results about percolation clusters on the hypercube to best-response dynamics in the random game.
--
--   **Formalization Note** The coupling is a measurable map $B$ from (payoffs, auxiliary configuration) to configurations, under the product of `gameMeasure μ N` and `percMeasure β N`; its push-forward is `percMeasure β N` and the equality of the two vertex sets holds for every point. The page's "for any $\beta\in[0,1/2]$" is automatic, since $\beta=\mathsf P(Z_1<Z_2)\le 1/2$ for every $\mu$.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 12, Proposition 4.1 (proof, p. 13)

import Mathlib
import Definitions.Def_RandomGames_BRD_Percolation

namespace RandomGames.BRD

open MeasureTheory

/-- Proposition 4.1, p. 12: with `β = P(Z₁ < Z₂)`, there is a bond percolation `B^β_N` on `H_N`,
built from the payoffs of `Ξ_N` and an independent auxiliary percolation with parameter `β`,
whose open cluster of `0` is exactly `L→^{β,0}_N`. -/
theorem proposition_4_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) :
    ∃ B : (Fin N → Profile N → ℝ) × (Edge N → Bool) → (Edge N → Bool),
      Measurable B ∧
      ((gameMeasure μ N).prod (percMeasure (beta μ) N)).map B = percMeasure (beta μ) N ∧
      ∀ x, cluster0 (B x) = reach0 x.1 := by sorry

end RandomGames.BRD
