-- Prove2me | Theorems.Thm_UncoupledDyn_Finite_theorem_1
-- name    : UncoupledDyn.Finite.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:39.107357+00:00
-- url     : https://prove2.me/theorems/1bc299d4-7b19-4058-8b0e-42f49adecd1f
-- title:
--   THEOREM 1 (§III case), pp. 1831–1833 — near Jordan's game Γ₀, no uncoupled dynamic is Nash-convergent
-- statement:
--   Consider three-player games in which each player has two strategies, with mixed-strategy state space $X=[0,1]^3$, and let $\Gamma_0$ be Jordan's game: player $i$ gets $1$ for playing $0$ against the next player's $1$, $1$ for playing $1$ against the next player's $0$, and $0$ otherwise (indices mod 3).
--
--   Let $\mathcal U$ be a family of such games with the single-Nash-equilibrium property (every $\Gamma\in\mathcal U$ has exactly one Nash equilibrium), and suppose that for some $\eta>0$ every game of Jordan's family $\mathcal U_0$ in the $\eta$-neighborhood of $\Gamma_0$ belongs to $\mathcal U$. Let $F$ be an uncoupled dynamic for $\mathcal U$. Then
--   $$F\ \text{is not Nash-convergent for}\ \mathcal U .$$
--   That is, there is a game $\Gamma\in\mathcal U$ with Nash equilibrium $\bar x$ such that one of the following fails: $F(\bar x;\Gamma)=0$; $F(\cdot;\Gamma)$ is $C^1$ on $X$; every eigenvalue of the Jacobian of $F(\cdot;\Gamma)$ at $\bar x$ has negative real part; every solution $x:[0,\infty)\to X$ of $\dot x=F(x;\Gamma)$ converges to $\bar x$.
--
--   This is the paper's Theorem 1 ("Let $\mathcal U$ be a family of games containing a neighborhood of the game $\Gamma_0$. Then every uncoupled dynamic for $\mathcal U$ is not Nash-convergent") for the finite game $\Gamma_0$ of §III: adaptive dynamics in which each player's motion depends only on its own payoff function cannot be guaranteed to converge to Nash equilibrium, even in a family where every game has a unique equilibrium and the coupled dynamic $\dot x=\bar x(\Gamma)-x$ does converge.
--
--   **Formalization Note.** The page's hypothesis "$\mathcal U$ contains a neighborhood of $\Gamma_0$" is replaced by the weaker "$\mathcal U$ contains every game of $\mathcal U_0$ in some fn.-7 neighborhood of $\Gamma_0$"; the page's hypothesis implies it, so the formal statement is at least as strong as the page's, and the Appendix (p. 1835) explicitly reads the neighborhood relative to $\mathcal U_0$. The single-Nash-equilibrium property of $\mathcal U$, a standing assumption of §I, is a hypothesis. Solutions are required to stay in $X$, and the C¹ and hyperbolic-stability requirements that §I places on the dynamics are clauses of Nash-convergence. Players are 0-based.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1831, THEOREM 1; §III, pp. 1832–1833

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix
import Definitions.Def_UncoupledDyn_Finite_Setting

namespace UncoupledDyn.Finite

theorem theorem_1 (U : Set Game) (hU : ∀ G ∈ U, ∃! x, IsNash G x)
    (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ))
    (hnbhd : ∃ η > 0, ∀ a : Fin 3 → ℝ, IsNear (jordanGame a) Gamma0 η → jordanGame a ∈ U)
    (hF : Uncoupled U F) :
    ¬ NashConvergent U F := by sorry

end UncoupledDyn.Finite
