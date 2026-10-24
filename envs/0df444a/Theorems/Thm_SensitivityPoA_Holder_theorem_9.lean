-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_theorem_9
-- name    : SensitivityPoA.Holder.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:32.622588+00:00
-- url     : https://prove2.me/theorems/b83238dd-b509-49c8-a4ae-65fe2a2cd294
-- title:
--   Theorem 9, p. 26 — at a game with costs Lipschitz on [0, T(d)], the PoA is Hölder continuous with exponent 1/2 on a ball around it
-- statement:
--   Fix a network satisfying the standing assumptions, and let $\Gamma = (\tau, d)$ be a game of the game space $\mathcal G(G,\mathcal K,\mathcal S)$ whose cost functions $\tau_a$ are Lipschitz continuous on $[0, T(d)]$ with a common Lipschitz constant $M$. Then there are constants $\epsilon_\Gamma > 0$ and $\kappa_\Gamma > 0$, depending only on $\Gamma$, such that every game $\Gamma'$ of the game space with $\|\Gamma - \Gamma'\| < \epsilon_\Gamma$ satisfies
--   $$|\rho(\Gamma) - \rho(\Gamma')| \le \kappa_\Gamma\,\|\Gamma - \Gamma'\|^{1/2}.$$
--
--   That is, the price of anarchy is pointwise Hölder continuous with exponent $1/2$ at every game with Lipschitz costs, with the ball $B_{\epsilon_\Gamma}(\Gamma)$ as a $\tfrac12$-neighborhood (Definition 3.1 and p. 24). Demands and cost functions may change simultaneously.
--
--   **Formalization Note** $\|\Gamma - \Gamma'\|$ is the distance (3.3). The constants are quantified before $\Gamma'$, so they depend on $\Gamma$ (and the Lipschitz constant $M$) only; $\Gamma'$ ranges over the game space, where $\rho$ is a genuine ratio of positive costs. A family of Lipschitz constants $M_a$ is equivalent to one common constant $M = \max_a M_a$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 26, Theorem 9; Definition 3.1 (p. 21) and γ-neighborhoods (p. 24)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Theorem 9, p. 26: at a game whose costs are Lipschitz on `[0, T(d)]`, the PoA is Hölder
continuous with exponent 1/2 on a ball `B_ε(Γ)` of the game space; `ε` and `κ` depend only on `Γ`. -/
theorem theorem_9 (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (M : ℝ) (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) :
    ∃ ε > 0, ∃ κ > 0, ∀ Γ' ∈ gameSpace N, gameDist Γ Γ' < ε →
      |PoA Γ - PoA Γ'| ≤ κ * Real.sqrt (gameDist Γ Γ') := by sorry

end SensitivityPoA.Holder
