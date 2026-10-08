-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_lemma_2_near
-- name    : UncoupledDyn.Continuum.lemma_2_near
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:39.117778+00:00
-- url     : https://prove2.me/theorems/18429ce3-0647-4959-ac0b-b065d33f0383
-- title:
--   Appendix, p. 1835 — Lemma 2's conclusions at Γ₀ hold for families containing the games of 𝒰₀ near Γ₀
-- statement:
--   Let $\mathcal U$ be a family of games, each with a single Nash equilibrium, which contains every game of $\mathcal U_0$ in some $\eta$-neighborhood of $\Gamma_0$ ($\eta>0$). Let $F$ be a dynamic for $\mathcal U$ that is uncoupled and Nash-convergent, and put $f^i(x)=F^i(x;u_0^i)$. Then for each player $i$ (with $j=3-i$):
--   1. $f^i(2x^j,x^j)=0$ for all $x^j$ in a neighborhood of $0$;
--   2. all eigenvalues of $J^i=(\partial f^i_k(0,0)/\partial x^i_l)_{k,l=1,2}$ have negative real parts.
--
--   These are exactly the two uses of Lemma 2 in the argument of §II; the Appendix obtains them from games of $\mathcal U_0$ that are close to $\Gamma_0$ instead of from the whole family $\mathcal U_0$.
--
--   **Formalization Note.** "$\mathcal U$ is a neighborhood of $\Gamma_0$" is encoded as the Appendix reads it, "certain to contain only those games in $\mathcal U_0$ that are close to $\Gamma_0$": $\mathcal U$ contains every game of $\mathcal U_0$ within $\eta$ of $\Gamma_0$ (fn. 7). This is implied by containing a full $\eta$-neighborhood; the full neighborhood together with the single-equilibrium property would be contradictory. Derivatives are within $X$; players are 0-based.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1835, Appendix, "The games corresponding to (φ, ψ_{yʲ}) and to (ψ_{xⁱ}, ψ_{yʲ}) … we can use them to obtain the result of Lemma 2 [by (2)]"; p. 1832, the two uses of Lemma 2

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- Appendix, p. 1835: let `𝒰` have the single-Nash-equilibrium property and contain every game
of `𝒰₀` close to `Γ₀`, and let `F` be uncoupled and Nash-convergent for `𝒰`. Then the two
conclusions of Lemma 2 used in §II hold for `fⁱ = Fⁱ( · ; u₀ⁱ)`: `fⁱ(2xʲ, xʲ) = 0` for `xʲ` near `0`,
and `Jⁱ = (∂fⁱ_k(0,0)/∂xⁱ_l)_{k,l}` has only eigenvalues with negative real parts. -/
theorem lemma_2_near (U : Set Game) (hU : ∀ G ∈ U, ∃! x, IsNash G x)
    (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ))
    (hnbhd : ∃ η > (0 : ℝ), ∀ G ∈ U0, IsNear G Gamma0 η → G ∈ U)
    (hF : Uncoupled U F) (hNC : NashConvergent U F) :
    (∀ i : Fin 2, ∀ᶠ w in nhds (0 : ℂ),
        F (fun m => if m = i then 2 * w else w) Gamma0 i = 0) ∧
      ∀ i : Fin 2, FatkhullinPolyak.Discrete.IsHurwitz (ownJac F Gamma0 i 0) := by sorry

end UncoupledDyn.Continuum
