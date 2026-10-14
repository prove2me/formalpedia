-- Prove2me | Theorems.Thm_STVFriedmann_theorem9_non_self_similar_blowup
-- name    : STVFriedmann.theorem9_non_self_similar_blowup
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:02:11.734909+00:00
-- url     : https://prove2.me/theorems/6b7d3c73-2951-4b91-9047-bd3b42f308cb
-- title:
--   Theorem 9 (n = 2): non-self-similar blow-up at the Big Bang
-- statement:
--   Fix $\Delta_0>0$. There is a solution $(z_2,w_0,z_4,w_2)(\bar t)$, $\bar t\in(0,\infty)$, of the order-2 STV ODE (2.48)–(2.51) such that
--
--   1. it agrees exactly with the $k=-1$ Friedmann spacetime at leading order: $(z_2,w_0)(\bar t)=(\tilde z_2(\theta),\tilde w_0(\theta))$ whenever $\bar t=\tfrac{\Delta_0}2(\sinh2\theta-2\theta)$, $\theta>0$ (notation of (2.41));
--   2. it tends to the Minkowski rest point $M=(0,1,0,0)$ as $\bar t\to\infty$;
--   3. it blows up at the Big Bang: $\|(z_2,w_0,z_4,w_2)(\bar t)\|\to\infty$ as $\bar t\to0^+$.
--
--   So, with time since the Big Bang imposed, solutions in $\mathcal F$ have a self-similar Big Bang at order $n=1$ (they tend to $SM$, Theorem 5) but need not at order $n=2$: such a solution misses $SM$ in backward time.
--
--   **Formalization Note** Solutions are functions of log-time $\tau=\ln\bar t$; $\|\cdot\|$ is the sup norm on $\mathbb R^4$.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 20, Theorem 9; p. 18 (solutions in F not in the unstable manifold of SM); p. 19, Section 2.8

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Theorem 9 at order 2: there are solutions of the order-2 STV ODE that agree exactly with
the `k = -1` Friedmann spacetime at leading order and decay to `M` as `t̄ → ∞`, but blow up
(instead of tending to `SM`) as `t̄ → 0⁺`. -/
theorem theorem9_non_self_similar_blowup (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) :
    ∃ U : ℝ → Fin 4 → ℝ, IsSTVSolution stvField2 U ∧
      (∀ θ : ℝ, 0 < θ → U (Real.log (Δ₀ * bigBangTime θ)) 0 = friedmannZ2 θ ∧
        U (Real.log (Δ₀ * bigBangTime θ)) 1 = friedmannW0 θ) ∧
      Tendsto U atTop (𝓝 restM2) ∧
      Tendsto (fun τ => ‖U τ‖) atBot atTop := by sorry

end STVFriedmann
