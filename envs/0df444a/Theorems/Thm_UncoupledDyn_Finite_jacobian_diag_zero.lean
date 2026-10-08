-- Prove2me | Theorems.Thm_UncoupledDyn_Finite_jacobian_diag_zero
-- name    : UncoupledDyn.Finite.jacobian_diag_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:35.814465+00:00
-- url     : https://prove2.me/theorems/94089d92-bd83-4154-9ed4-cff93edbd275
-- title:
--   §III, p. 1833 — for an uncoupled Nash-convergent dynamic, fⁱ vanishes along the i-th axis through x̄₀, so diag J = 0 and tr J = 0
-- statement:
--   Let $\mathcal U$ be a family of three-player games in which every game has a single Nash equilibrium, and suppose $\mathcal U$ contains every game of Jordan's family that is close to $\Gamma_0$: for some $\eta>0$, every $\Gamma_a$ in the $\eta$-neighborhood of $\Gamma_0$ belongs to $\mathcal U$. Let $F$ be an uncoupled dynamic for $\mathcal U$ that is Nash-convergent for $\mathcal U$. Write $f^i(x)=F^i(x;\Gamma_0)$, $\bar x_0=(1/2,1/2,1/2)$, and let $J$ be the Jacobian matrix of $f$ at $\bar x_0$. Then:
--
--   1. for every player $i$ and every $y$ close to $1/2$, $f^i$ vanishes at the point whose $i$-th coordinate is $y$ and whose other coordinates are $1/2$;
--   2. every diagonal entry of $J$ vanishes: $\partial f^i(\bar x_0)/\partial x^i=0$ for $i=1,2,3$;
--   3. consequently
--   $$\operatorname{tr} J=0 .$$
--
--   This is the core of the §III proof of Theorem 1: uncoupledness transports the rest-point condition from nearby games of the family back to $\Gamma_0$, which pins down the diagonal of the Jacobian.
--
--   **Formalization Note.** The hypotheses that $F$ is uncoupled and Nash-convergent are the assumptions the page makes "by way of contradiction". The neighborhood hypothesis asks only that the games of Jordan's family near $\Gamma_0$ lie in $\mathcal U$; it is implied by the page's "$\mathcal U$ contains a neighborhood of $\Gamma_0$". Players are 0-based. The Jacobian is the derivative within $X=[0,1]^3$ (at the interior point $\bar x_0$ it is the ordinary derivative).
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), p. 1833, §III, proof of Theorem 1, second paragraph

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix
import Definitions.Def_UncoupledDyn_Finite_Setting

namespace UncoupledDyn.Finite

theorem jacobian_diag_zero (U : Set Game) (hU : ∀ G ∈ U, ∃! x, IsNash G x)
    (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ))
    (hnbhd : ∃ η > 0, ∀ a : Fin 3 → ℝ, IsNear (jordanGame a) Gamma0 η → jordanGame a ∈ U)
    (hF : Uncoupled U F) (hNC : NashConvergent U F) :
    (∀ i : Fin 3, ∀ᶠ y in nhds (1 / 2 : ℝ),
        F (Function.update (fun _ : Fin 3 => (1 / 2 : ℝ)) i y) Gamma0 i = 0) ∧
    (∀ i : Fin 3, jac F Gamma0 (fun _ => 1 / 2) i i = 0) ∧
    (jac F Gamma0 (fun _ => 1 / 2)).trace = 0 := by sorry

end UncoupledDyn.Finite
