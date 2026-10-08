-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_lemma_2
-- name    : UncoupledDyn.Continuum.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:20.162676+00:00
-- url     : https://prove2.me/theorems/eebcbeb6-4414-4312-b3ba-8ff176797c22
-- title:
--   LEMMA 2, p. 1832 — at a unique best reply, Fⁱ vanishes and the own-strategy Jacobian Jⁱ is stable
-- statement:
--   Let $F$ be a dynamic for the family $\mathcal U_0$ that is uncoupled and Nash-convergent. Let $\Gamma\in\mathcal U_0$, let $i$ be a player with payoff function $u^i$ in $\Gamma$, and let $y=(y^i,y^j)\in D\times D$ be such that $y^i$ is the unique $u^i$-best reply of $i$ to $y^j$:
--   $$u^i(y^i,y^j)>u^i(x^i,y^j)\qquad\text{for all }x^i\in D,\ x^i\ne y^i.$$
--   Then $F^i(y^i,y^j;u^i)=0$, and all eigenvalues of the $2\times2$ Jacobian matrix
--   $$J^i=\left(\frac{\partial F^i_k(y^i,y^j;u^i)}{\partial x^i_l}\right)_{k,l=1,2}$$
--   have negative real parts.
--
--   This is the key lemma of the proof: it turns uncoupledness into information about player $i$'s component of the dynamic, which is all that the argument at $\Gamma_0$ uses.
--
--   **Formalization Note.** $F^i(y;u^i)$ is evaluated in the game $\Gamma$ itself; by uncoupledness every game of $\mathcal U_0$ with the same $u^i$ gives the same value. Partial derivatives are taken within $X=D\times D$, so the statement covers profiles on the boundary of $X$. Coordinates $k,l=1,2$ are the real and imaginary parts, and players are 0-based.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1832, LEMMA 2 and fn. 11

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- LEMMA 2, p. 1832: let `F` be an uncoupled, Nash-convergent dynamic for `𝒰₀`. If `yⁱ` is the
unique `uⁱ`-best reply of `i` to `yʲ` in a game of `𝒰₀` with payoff `uⁱ` for `i`, then
`Fⁱ(yⁱ, yʲ; uⁱ) = 0` and the `2 × 2` matrix `Jⁱ = (∂Fⁱ_k(yⁱ, yʲ; uⁱ)/∂xⁱ_l)_{k,l}` has only
eigenvalues with negative real parts. -/
theorem lemma_2 (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) (hF : Uncoupled U0 F)
    (hNC : NashConvergent U0 F) (G : Game) (hG : G ∈ U0) (i : Fin 2) (y : Fin 2 → ℂ)
    (hy : y ∈ X) (hbest : ∀ z ∈ D, z ≠ y i → G i (Function.update y i z) < G i y) :
    F y G i = 0 ∧ FatkhullinPolyak.Discrete.IsHurwitz (ownJac F G i y) := by sorry

end UncoupledDyn.Continuum
