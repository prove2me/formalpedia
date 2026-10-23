-- Prove2me | Theorems.Thm_RandomGames_BRD_proposition_4_2
-- name    : RandomGames.BRD.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:02.04822+00:00
-- url     : https://prove2.me/theorems/e72e7f6a-40c3-4a68-bc05-e674745c84a1
-- title:
--   Proposition 4.2, p. 14, in the form (4.7) — summably in N, the open cluster of 0 is the giant component of percolation on the hypercube
-- statement:
--   Let $\beta\in(0,1/2]$ and consider bond percolation $\mathscr B^\beta_N$ on the hypercube $\mathscr H_N$. Then
--   $$\sum_{N=1}^\infty \mathsf P\bigl(\mathscr L^\beta_N\neq\mathscr L^{\beta,\mathbf 0}_N\bigr) < \infty, \tag{4.7}$$
--   where $\mathscr L^\beta_N$ is the giant component and $\mathscr L^{\beta,\mathbf 0}_N$ the open cluster of $\mathbf 0$.
--
--   By the coupling of Proposition 4.1 this is equivalent to the paper's statement (4.6), $\sum_N\mathsf P(\mathscr L^\beta_N\neq\vec{\mathscr L}^{\beta,\mathbf 0}_N)<\infty$: by the first Borel–Cantelli lemma, for all large $N$ the profiles accessible from $\mathbf 0$ form the giant component.
--
--   **Formalization Note** The statement is the percolation-only form (4.7) to which the paper's proof reduces (4.6) through Proposition 4.1; under that coupling the two events coincide pointwise. The event $\mathscr L^\beta_N\neq\mathscr L^{\beta,\mathbf 0}_N$ is `NotInGiant`: some cluster not containing $\mathbf 0$ is at least as large as the cluster of $\mathbf 0$. On a tie for the largest cluster this counts $\mathbf 0$ as outside the giant, so the statement implies (4.7) for every tie rule.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 14, Proposition 4.2, (4.6), (4.7)

import Mathlib
import Definitions.Def_RandomGames_BRD_Percolation

namespace RandomGames.BRD

open MeasureTheory

/-- Proposition 4.2, p. 14, in the form (4.7) to which its proof reduces (4.6) via
Proposition 4.1: for `β ∈ (0, 1/2]`, `∑_N P(L^β_N ≠ L^{β,0}_N) < ∞`, where on a tie for the
largest open cluster `0` counts as outside the giant component. -/
theorem proposition_4_2 (β : ℝ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) :
    ∑' N, percMeasure β N {ω | NotInGiant ω} ≠ ⊤ := by sorry

end RandomGames.BRD
