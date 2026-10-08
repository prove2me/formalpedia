-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_theorem_1
-- name    : UncoupledDyn.Continuum.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:33.158101+00:00
-- url     : https://prove2.me/theorems/ef5d7540-aa8e-43ef-9787-87d93704b963
-- title:
--   THEOREM 1 (§II case), p. 1831 — near the unit-disk game Γ₀, no uncoupled dynamic is Nash-convergent
-- statement:
--   Consider two-player games in which each player's strategy set is the closed unit disk $D\subset\mathbb R^2$, and let $\Gamma_0$ be the game of §II with payoffs $u_0^i(x^i,x^j)=-\|x^i-\varphi(x^j)\|^2$, where $\varphi(z)=2z$ for $\|z\|\le\frac13$, $\varphi$ rotates the unit circle by $\pi/4$, and $\varphi$ is affine on rays in between.
--
--   Let $\mathcal U$ be a family of games in which every game has a single Nash equilibrium, and suppose that $\mathcal U$ contains a neighborhood of $\Gamma_0$, in the sense that for some $\eta>0$ it contains every game of $\mathcal U_0$ whose payoffs differ from those of $\Gamma_0$ by less than $\eta$ at every profile. Then
--
--   $$\text{every uncoupled dynamic for }\mathcal U\text{ is not Nash-convergent.}$$
--
--   Here a dynamic $\dot x=F(x;\Gamma)$ is uncoupled if each $F^i$ depends on the game only through player $i$'s own payoff function $u^i$, and Nash-convergent if, for every game of $\mathcal U$, $F$ is $C^1$, the Nash equilibrium $\bar x$ is a rest point at which the Jacobian has only eigenvalues with negative real parts, and every solution converges to $\bar x$. The theorem says that dynamics in which each player reacts only to their own payoffs cannot guarantee convergence to Nash equilibrium, even on an arbitrarily small family of games with unique equilibria.
--
--   **Formalization Note.** The family $\mathcal U_0$ consists of the games $u^i(x^i,x^j)=-\|x^i-\xi^i(x^j)\|^2$ with continuous $\xi^i:D\to D$ for which $\xi^i(\xi^j(x^i))=x^i$ has a unique solution; $\Gamma_0\in\mathcal U_0$. The hypothesis "contains a neighborhood of $\Gamma_0$" is the Appendix's reading ("certain to contain only those games in $\mathcal U_0$ that are close to $\Gamma_0$"); it is implied by containing a full fn. 7 neighborhood, so the formal theorem is at least as strong as the page's. A full neighborhood would contain games with several equilibria, which together with the single-equilibrium hypothesis would make the hypotheses contradictory. Both hypotheses can be met, e.g. by $\mathcal U=\{\Gamma\in\mathcal U_0:\ \Gamma\text{ within }1\text{ of }\Gamma_0\}$. The single-equilibrium property is a hypothesis (§I). Solutions are curves in $X=D\times D$; derivatives are within $X$; Nash equilibria are pure; players are 0-based; $\mathbb R^2$ is $\mathbb C$.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1831, THEOREM 1; §II, pp. 1831–1832; Appendix, p. 1835

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- THEOREM 1 (§II case), p. 1831: let `𝒰` be a family of games, each with a single Nash
equilibrium, containing every game of `𝒰₀` close enough to `Γ₀`. Then every uncoupled dynamic for
`𝒰` is not Nash-convergent. -/
theorem theorem_1 (U : Set Game) (hU : ∀ G ∈ U, ∃! x, IsNash G x)
    (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ))
    (hnbhd : ∃ η > (0 : ℝ), ∀ G ∈ U0, IsNear G Gamma0 η → G ∈ U)
    (hF : Uncoupled U F) : ¬ NashConvergent U F := by sorry

end UncoupledDyn.Continuum
