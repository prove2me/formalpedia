-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_U0_unique_nash
-- name    : UncoupledDyn.Continuum.U0_unique_nash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:21.66199+00:00
-- url     : https://prove2.me/theorems/bb49004e-0dfa-4f4b-90a8-0ab4a04d6dd7
-- title:
--   §II, p. 1831 — every game of 𝒰₀ has the unique Nash equilibrium (x̄¹, x̄²), x̄ⁱ the solution of ξⁱ(ξʲ(xⁱ)) = xⁱ
-- statement:
--   Let $\xi^1,\xi^2:D\to D$ be continuous maps of the closed unit disk such that, for each $i$ (with $j=3-i$), the equation
--   $$\xi^i(\xi^j(x^i))=x^i$$
--   has a unique solution $x^i\in D$, and let $\bar x^i$ be that solution. Let $\Gamma$ be the game with payoffs $u^i(x^i,x^j)=-\|x^i-\xi^i(x^j)\|^2$ on $D\times D$, i.e. a game of the family $\mathcal U_0$. Then $\bar x=(\bar x^1,\bar x^2)$ is a Nash equilibrium of $\Gamma$, and it is the only one.
--
--   This is the single-Nash-equilibrium property of the family $\mathcal U_0$ in which the paper embeds $\Gamma_0$.
--
--   **Formalization Note.** Players are 0-based (the page's $j=3-i$ is `i + 1` in `Fin 2`). The game is required to have the stated payoffs on $X=D\times D$ only. Nash equilibrium is pure (fn. 9).
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1831, §II, "We embed Γ₀ in the family 𝒰₀ … Then x̄ = (x̄¹, x̄²) is the unique Nash equilibrium of the game Γ"

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- §II, p. 1831: if `uⁱ(xⁱ, xʲ) = −‖xⁱ − ξⁱ(xʲ)‖²` with continuous `ξⁱ : D → D` such that
`ξⁱ(ξʲ(xⁱ)) = xⁱ` has a unique solution, and `x̄ⁱ` is that solution (`i = 1, 2`), then
`x̄ = (x̄¹, x̄²)` is the unique Nash equilibrium of the game. -/
theorem U0_unique_nash (ξ : Fin 2 → ℂ → ℂ)
    (hξ : ∀ i, ContinuousOn (ξ i) D ∧ Set.MapsTo (ξ i) D D)
    (huniq : ∀ i, ∃! z, z ∈ D ∧ ξ i (ξ (i + 1) z) = z)
    (G : Game) (hG : ∀ i, ∀ x ∈ X, G i x = -‖x i - ξ i (x (i + 1))‖ ^ 2)
    (xbar : Fin 2 → ℂ) (hxbar : ∀ i, xbar i ∈ D ∧ ξ i (ξ (i + 1) (xbar i)) = xbar i) :
    IsNash G xbar ∧ ∀ x, IsNash G x → x = xbar := by sorry

end UncoupledDyn.Continuum
