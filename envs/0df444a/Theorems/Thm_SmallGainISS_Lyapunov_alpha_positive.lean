-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_alpha_positive
-- name    : SmallGainISS.Lyapunov.alpha_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:26.618065+00:00
-- url     : https://prove2.me/theorems/6e2a2c8c-82ca-4f95-b5f5-1734367cb9b6
-- title:
--   Proof of Theorem 5.3, p. 15: on $\|x\|=r$, the active blocks satisfy $\|x_i\|\ge\delta(r)>0$
-- statement:
--   Let $V_1,\dots,V_n$ ($n\ge1$) satisfy Assumption 2.1, let $\sigma_i\in\mathcal K_\infty$ with inverses $\sigma_i^{-1}$, and let $V(x)=\max_i\sigma_i^{-1}(V_i(x_i))$. For every $r>0$ there is $\delta>0$ such that
--   $$\|x\|=r\ \text{ and }\ V(x)=\sigma_i^{-1}(V_i(x_i))\ \Longrightarrow\ \|x_i\|\ge\delta .$$
--
--   This is the fact used on p. 15 to see that the decrease rate $\alpha(r)=\min\{\tilde\alpha_i(\|x_i\|): \|x\|=r,\ V(x)=\sigma_i^{-1}(V_i(x_i))\}$ is positive.
--
--   **Formalization Note** $\|x\|$ is the Euclidean norm on $\mathbb R^N$, $\|x\|^2=\sum_i\|x_i\|^2$.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 15, proof of Theorem 5.3 (definition of α)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- The positivity claim behind the definition of `α` in the proof of Theorem 5.3 (p. 15): "for a
given `r > 0` and `‖x‖ = r` the norm of `‖xᵢ‖` such that `V(x) = σᵢ⁻¹(Vᵢ(xᵢ))` is bounded
away from 0": for every `r > 0` there is `δ > 0` such that `δ ≤ ‖xᵢ‖` whenever `‖x‖ = r` and
`i` is active at `x`. -/
theorem alpha_positive {n : ℕ} [NeZero n] {N : Fin n → ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (hV : ∀ j, IsLyapCandidate (Vb j))
    (hσ : ∀ i, IsKInf (fun r => σ r i))
    (hτ : ∀ i, IsInverse (τ i) (fun r => σ r i)) :
    ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ∀ x : State N, ‖x‖ = r →
      ∀ i ∈ activeSet Vb τ x, δ ≤ ‖x i‖ := by sorry

end SmallGainISS.Lyapunov
