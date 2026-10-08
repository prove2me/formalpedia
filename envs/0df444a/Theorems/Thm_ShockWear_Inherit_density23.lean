-- Prove2me | Theorems.Thm_ShockWear_Inherit_density23
-- name    : ShockWear.Inherit.density23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:14.125977+00:00
-- url     : https://prove2.me/theorems/ad681230-6bc8-481c-b231-d9ea2ca141a0
-- title:
--   Equation (2.3) — positive-time density of the Poisson shock life
-- statement:
--   Let shocks arrive at rate $\lambda>0$, and let $1\geq\bar P_0\geq\bar P_1\geq\cdots\geq0$ be their survival probabilities. Write $\bar H$ for the Poisson mixture (2.1), $p_{k+1}=\bar P_k-\bar P_{k+1}$, and $h$ for the series (2.3). At every positive time $t$,
--
--   $$\bar H'(t)=-h(t),\qquad h(t)=\lambda\sum_{k\geq0}p_{k+1}e^{-\lambda t}(\lambda t)^k/k!.$$
--
--   This identifies the density away from the possible mass $1-\bar P_0$ at time zero and supports the subsequent hazard-rate calculations.
--
--   **Formalization Note** The derivative identity is the positive-time content of the density formula. Nonnegativity and weak monotonicity of the probabilities are explicit, and the series is reindexed from $k=1$ to $k=0$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 628, (2.1)–(2.3); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- Formula (2.3): the derivative of survival at positive time is minus the density. -/
theorem density23 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 < t → HasDerivAt (ShockWear.CumDamage.shockSurv lam P) (-shockDens lam P t) t := by sorry

end ShockWear.Inherit
