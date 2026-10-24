-- Prove2me | Theorems.Thm_SensitivityPoA_Lipschitz_ineq_4_33
-- name    : SensitivityPoA.Lipschitz.ineq_4_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:53.042587+00:00
-- url     : https://prove2.me/theorems/44733f4e-b1bd-4643-830e-589a47165739
-- title:
--   (4.33), p. 37 — near a game with costs constant on [0, T(d)], 0 ≤ ρ(Γ′) − ρ(Γ) ≤ 8·|A|·T(d)·(|K|+1)/C∗(Γ)·‖Γ − Γ′‖
-- statement:
--   Let $\Gamma=(\tau,d)$ be a game in the game space $\mathcal G(G,K,S)$ whose arc costs are constant on $[0,T(d)]$. Then there is $\delta>0$ such that every game $\Gamma'\in\mathcal G(G,K,S)$ with $\|\Gamma-\Gamma'\|<\delta$ satisfies
--   $$0\le\rho(\Gamma')-\rho(\Gamma)\le\frac{8\cdot|A|\cdot T(d)\cdot(|K|+1)}{C^*(\Gamma)}\cdot\|\Gamma-\Gamma'\|.$$
--   Here $|A|$ is the number of arcs, $|K|$ the number of O/D pairs, $T(d)$ the total demand of $\Gamma$, $C^*(\Gamma)$ its social optimum cost and $\|\Gamma-\Gamma'\|$ the distance (3.3).
--
--   This is the explicit form of Theorem 12a): near a game with constant costs the price of anarchy can only increase, and at most linearly in the distance, with a constant depending only on $\Gamma$.
--
--   **Formalization Note** The paper prints the last inequality strictly ("$<$"), which fails at $\Gamma'=\Gamma$ (both sides $0$); the non-strict reading is posed. "When $\|\Gamma-\Gamma'\|$ is small" is rendered as the existence of a threshold $\delta>0$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 37, display (4.33)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting
import Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts

namespace SensitivityPoA.Lipschitz

theorem ineq_4_33 (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (hc : ConstOnDemand Γ) :
    ∃ δ > 0, ∀ Γ' ∈ gameSpace N, gameDist Γ Γ' < δ →
      0 ≤ PoA Γ' - PoA Γ ∧
      PoA Γ' - PoA Γ ≤
        8 * (N.J : ℝ) * totalDemand Γ.d * ((N.Sd : ℝ) + 1) / SOCost Γ * gameDist Γ Γ' := by sorry

end SensitivityPoA.Lipschitz
