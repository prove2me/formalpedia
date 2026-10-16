-- Prove2me | Theorems.Thm_SensitivityPoA_Lipschitz_theorem_12
-- name    : SensitivityPoA.Lipschitz.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:38.028789+00:00
-- url     : https://prove2.me/theorems/1522b6ee-c949-402f-9007-443725b3a7c8
-- title:
--   Theorem 12, pp. 36–37 — the PoA is locally Lipschitz at games with costs constant, or C¹ with derivative ≥ m > 0, on [0, T(d)]
-- statement:
--   Let $\Gamma=(\tau,d)$ be a game in the game space $\mathcal G(G,K,S)$, with price of anarchy $\rho(\Gamma)$ and distance $\|\cdot\|$ of (3.3).
--
--   1. If $\tau_a(x)$ is constant in $x\in[0,T(d)]$ for every arc $a$, then there are $\epsilon_\Gamma>0$ and $\kappa_\Gamma>0$ such that
--   $$|\rho(\Gamma)-\rho(\Gamma')|\le\kappa_\Gamma\cdot\|\Gamma-\Gamma'\|\qquad\text{for every }\Gamma'\in\mathcal G(G,K,S)\text{ with }\|\Gamma-\Gamma'\|<\epsilon_\Gamma.$$
--   2. If every $\tau_a$ is continuously differentiable on $[0,T(d)]$ with $\tau_a'(x)\ge m_\Gamma$ for all $x\in[0,T(d)]$, for some constant $m_\Gamma>0$, then the same conclusion holds: there are $\epsilon_\Gamma>0$ and $\kappa_\Gamma>0$ with $|\rho(\Gamma)-\rho(\Gamma')|\le\kappa_\Gamma\cdot\|\Gamma-\Gamma'\|$ for every game $\Gamma'$ with $\|\Gamma-\Gamma'\|<\epsilon_\Gamma$.
--
--   In both cases the price of anarchy is pointwise Hölder continuous at $\Gamma$ with exponent $1$ (locally Lipschitz), an improvement over the exponent $1/2$ that holds at every game with Lipschitz costs. The perturbed game $\Gamma'$ may change demands and costs simultaneously.
--
--   **Formalization Note** The paper prints the conclusion strictly, "$|\rho(\Gamma)-\rho(\Gamma')|<\kappa_\Gamma\cdot\|\Gamma-\Gamma'\|$", which fails at $\Gamma'=\Gamma$ (and at every $\Gamma'$ at distance $0$ from $\Gamma$); the non-strict reading is posed. The constants $\epsilon_\Gamma,\kappa_\Gamma$ are chosen after $\Gamma$ (and after $m_\Gamma$ in part 2) and before $\Gamma'$. The hypotheses concern $[0,T(d)]$ only; costs beyond $T(d)$ are arbitrary elements of the game space. The derivative in part 2 is one-sided at the endpoints of $[0,T(d)]$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 36–37, Theorem 12

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting
import Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts

namespace SensitivityPoA.Lipschitz

theorem theorem_12 (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N) :
    (ConstOnDemand Γ →
      ∃ ε > 0, ∃ κ > 0, ∀ Γ' ∈ gameSpace N, gameDist Γ Γ' < ε →
        |PoA Γ - PoA Γ'| ≤ κ * gameDist Γ Γ') ∧
    (∀ m : ℝ, 0 < m → C1SlopeOnDemand Γ m →
      ∃ ε > 0, ∃ κ > 0, ∀ Γ' ∈ gameSpace N, gameDist Γ Γ' < ε →
        |PoA Γ - PoA Γ'| ≤ κ * gameDist Γ Γ') := by sorry

end SensitivityPoA.Lipschitz
