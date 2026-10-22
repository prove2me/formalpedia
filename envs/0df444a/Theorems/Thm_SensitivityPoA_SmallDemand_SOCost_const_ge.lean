-- Prove2me | Theorems.Thm_SensitivityPoA_SmallDemand_SOCost_const_ge
-- name    : SensitivityPoA.SmallDemand.SOCost_const_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:15.74472+00:00
-- url     : https://prove2.me/theorems/f76d32f5-856c-4074-bcea-87cbf711e982
-- title:
--   p. 43 — the constant-cost game Γ′ = (σ, d/T(d)), σ_a ≡ τ_a(0), has SO cost C∗(Γ′) ≥ τmin(0)
-- statement:
--   Fix a structure satisfying the standing assumptions. Let $\tau = (\tau_a)_{a\in A}$ be functions with $\tau_a(0) > 0$ for every arc, and let
--   $$\tau_{\min}(0) = \min_{a \in A} \tau_a(0).$$
--   Let $d \ge 0$ be a demand vector with $T(d) > 0$, let $\sigma_a(x) \equiv \tau_a(0)$, and let $\Gamma' = (\sigma, d/T(d))$. Then
--   $$\mathcal C^*(\Gamma') \ge \tau_{\min}(0).$$
--
--   The lower bound does not depend on $d$, because $\Gamma'$ always has total demand $T(d/T(d)) = 1$; this uniformity is what makes the constant of Corollary 5.1 independent of the demand.
--
--   **Formalization Note** $\tau_{\min}(0)$ is passed as a real number that is the least element of $\{\tau_a(0) : a \in A\}$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 43, §5.2, "C∗(Γ′) ≥ τmin(0)"

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

namespace SensitivityPoA.SmallDemand

open KellyStochasticNetworks

/-- p. 43: with `σ_a ≡ τ_a(0) > 0` and `τmin(0) = min_a τ_a(0)`, the SO cost of the auxiliary game
`Γ' = (σ, d/T(d))` is at least `τmin(0)` for every demand vector `d`, since `T(d/T(d)) = 1`. -/
theorem SOCost_const_ge (N : Network) (hN : N.Standing) (τ : Fin N.J → ℝ → ℝ)
    (hpos : ∀ j, 0 < τ j 0) (τmin : ℝ) (hτmin : IsLeast (Set.range fun j => τ j 0) τmin)
    (d : Fin N.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) (hT : 0 < totalDemand d) :
    τmin ≤ SOCost (⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ : Game N) := by sorry

end SensitivityPoA.SmallDemand
