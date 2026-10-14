-- Prove2me | Theorems.Thm_STVFriedmann_theorem8_instability_order2
-- name    : STVFriedmann.theorem8_instability_order2
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:03:23.719651+00:00
-- url     : https://prove2.me/theorems/ba757f66-eb56-4c16-8f55-caed74141c7a
-- title:
--   Theorem 8 (n = 2): accelerations away from k < 0 Friedmann in the unstable manifold of SM
-- statement:
--   Fix $\Delta_0>0$ and consider the order-2 STV ODE (2.48)–(2.51). Let $\mathcal S$ be the set of solutions $U(\bar t)=(z_2,w_0,z_4,w_2)(\bar t)$, $\bar t\in(0,\infty)$, such that
--
--   1. $U(\bar t)\to SM=(\tfrac43,\tfrac23,\tfrac{40}{27},\tfrac29)$ as $\bar t\to0^+$ (the trajectory lies in the unstable manifold of $SM$);
--   2. $U(\bar t)\to M=(0,1,0,0)$ as $\bar t\to\infty$;
--   3. $U$ agrees exactly with the $k=-1$ Friedmann spacetime of parameter $\Delta_0$ at leading order: $(z_2,w_0)(\bar t)=(\tilde z_2(\theta),\tilde w_0(\theta))$ whenever $\bar t=\tfrac{\Delta_0}2(\sinh2\theta-2\theta)$, $\theta>0$ (notation of (2.41)).
--
--   Then $\mathcal S$ is a one-parameter family: there is an injective map $b\mapsto U_b$ from $\mathbb R$ onto $\mathcal S$, and $U_0$ is the projection of the $k=-1$ Friedmann spacetime onto the STV ODE of order 2,
--
--   $$
--   U_0(\bar t)=(\tilde z_2,\tilde w_0,\tilde z_4,\tilde w_2)(\theta)\quad\text{for } \bar t=\tfrac{\Delta_0}2(\sinh2\theta-2\theta).
--   $$
--
--   In particular every $U_b$ with $b\neq0$ takes $SM$ to $M$ and agrees with the $k<0$ Friedmann spacetime at leading order, but is distinct from it at order 2: it departs ("accelerates away") from the Friedmann spacetime at intermediate times. This is the order-2 case of Theorem 8, the order at which the instability of the critical Friedmann spacetime $SM$ first produces trajectories distinct from Friedmann spacetimes.
--
--   **Formalization Note** Solutions are functions of log-time $\tau=\ln\bar t\in\mathbb R$ satisfying $dU/d\tau=F_2(U)$; $\bar t\to0^+$ and $\bar t\to\infty$ are $\tau\to\mp\infty$. The family is required to be onto $\mathcal S$, so the statement also asserts that $\mathcal S$ contains nothing beyond this one-parameter family.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 19, Theorem 8 (case n = 2) and Section 2.8; p. 18 (unstable manifold of SM at order 2, eq. (2.52), parameter b)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Theorem 8 at order `n = 2` (main goal).  Fix `Δ₀ > 0` and let `S` be the set of solutions
`U` of the order-2 STV ODE that emanate from `SM` at the Big Bang (`t̄ → 0⁺`), decay to `M` as
`t̄ → ∞`, and agree exactly with the `k = -1` Friedmann spacetime of parameter `Δ₀` at leading
order.  Then `S` is a one-parameter family `b ↦ U_b` (an injective parametrization by `ℝ`),
and its member `U_0` is the `k = -1` Friedmann spacetime itself (at order 2). -/
theorem theorem8_instability_order2 (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) :
    ∃ family : ℝ → ℝ → Fin 4 → ℝ,
      Function.Injective family ∧
      Set.range family =
        {U : ℝ → Fin 4 → ℝ | IsSTVSolution stvField2 U ∧
          Tendsto U atBot (𝓝 restSM2) ∧ Tendsto U atTop (𝓝 restM2) ∧
          ∀ θ : ℝ, 0 < θ → U (Real.log (Δ₀ * bigBangTime θ)) 0 = friedmannZ2 θ ∧
            U (Real.log (Δ₀ * bigBangTime θ)) 1 = friedmannW0 θ} ∧
      ∀ θ : ℝ, 0 < θ → family 0 (Real.log (Δ₀ * bigBangTime θ)) = friedmannCurve2 θ := by
  sorry

end STVFriedmann
