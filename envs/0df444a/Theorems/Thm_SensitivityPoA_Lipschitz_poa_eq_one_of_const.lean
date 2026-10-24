-- Prove2me | Theorems.Thm_SensitivityPoA_Lipschitz_poa_eq_one_of_const
-- name    : SensitivityPoA.Lipschitz.poa_eq_one_of_const
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:27.410691+00:00
-- url     : https://prove2.me/theorems/ad7c2a7d-dc96-4d51-b518-5e870d95bbed
-- title:
--   p. 37, proof of Theorem 12a) — a game whose costs are constant on [0, T(d)] has price of anarchy 1
-- statement:
--   Let $\Gamma=(\tau,d)$ be a game in the game space $\mathcal G(G,K,S)$ whose arc costs are constant on the range of possible arc flows, $\tau_a(x)=\tau_a(0)$ for all arcs $a$ and all $x\in[0,T(d)]$. Then the Wardrop equilibrium cost equals the social optimum cost:
--   $$\rho(\Gamma)=\frac{\tilde C(\Gamma)}{C^*(\Gamma)}=1.$$
--
--   With constant costs, the cost of a path does not depend on the flow, so selfish and optimal routing both send every pair's demand along its cheapest paths. This is the base case of the local Lipschitz continuity of $\rho$ at such games (Theorem 12a)), and is used for the auxiliary game $\Gamma''$ in its proof.
--
--   **Formalization Note** The page states $\rho(\Gamma)=\rho(\Gamma'')=1$ for the given game $\Gamma$ (costs constant on $[0,T(d)]$) and for the auxiliary game $\Gamma''$ with costs $\hat\tau_a\equiv\tau_a(0)$ on $[0,\infty)$; both are instances of the statement posed here.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 37, proof of Theorem 12a), "Then ρ(Γ) = ρ(Γ′′) = 1"

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting
import Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts

namespace SensitivityPoA.Lipschitz

theorem poa_eq_one_of_const (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (hc : ConstOnDemand Γ) : PoA Γ = 1 := by sorry

end SensitivityPoA.Lipschitz
