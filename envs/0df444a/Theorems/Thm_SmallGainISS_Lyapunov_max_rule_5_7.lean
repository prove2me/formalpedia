-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_max_rule_5_7
-- name    : SmallGainISS.Lyapunov.max_rule_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:35.554629+00:00
-- url     : https://prove2.me/theorems/21292c26-6dda-4e5a-b78e-35f29c2e0f7c
-- title:
--   (5.7): $\partial V(x)\subset\mathrm{conv}\bigcup_{i\in I}\partial[\sigma_i^{-1}\circ V_i\circ\pi_i](x)$
-- statement:
--   In the setting of the previous statement (candidates $V_i$, $\sigma_i\in\mathcal K_\infty$ with locally Lipschitz inverses on $(0,\infty)$), let $V(x)=\max_i\sigma_i^{-1}(V_i(x_i))$ and, for $x\ne0$, let $I$ be the set of indices $i$ with $V(x)=\sigma_i^{-1}(V_i(x_i))$ (5.6). Write $\pi_i$ for the projection $x\mapsto x_i$ and $\partial$ for Clarke's generalized gradient (2.5). Then
--   $$\partial V(x)\subset\mathrm{conv}\Big\{\bigcup_{i\in I}\partial\big[\sigma_i^{-1}\circ V_i\circ\pi_i\big](x)\Big\}.$$
--
--   This is the maximum rule for generalized gradients, applied to the function (5.4); it reduces the decrease of $V$ to the decrease of the active rescaled subsystem functions.
--
--   **Formalization Note** $\partial$ on $\mathbb R^N$ is `clarkeGrad`, the Clarke gradient (2.5) on a general Hilbert space. $\sigma_i^{-1}\circ V_i\circ\pi_i$ is the real function $y\mapsto\sigma_i^{-1}(V_i(y_i))$.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 14, proof of Theorem 5.3, (5.6), (5.7)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- (5.7) (p. 14): at `x ≠ 0`, the Clarke generalized gradient of `V(x) = maxᵢ σᵢ⁻¹(Vᵢ(xᵢ))`
is contained in the convex hull of the union, over the active indices `i ∈ I` of (5.6), of the
generalized gradients of `σᵢ⁻¹ ∘ Vᵢ ∘ πᵢ` at `x` (`πᵢ` the projection onto block `i`). -/
theorem max_rule_5_7 {n : ℕ} [NeZero n] {N : Fin n → ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (hV : ∀ j, IsLyapCandidate (Vb j))
    (hσ : ∀ i, IsKInf (fun r => σ r i))
    (hτ : ∀ i, IsInverse (τ i) (fun r => σ r i))
    (hτL : ∀ i, LocallyLipschitzOn (Set.Ioi (0 : ℝ≥0)) (τ i))
    (x : State N) (hx : x ≠ 0) :
    clarkeGrad (netV Vb τ) x ⊆
      convexHull ℝ (⋃ i ∈ activeSet Vb τ x,
        clarkeGrad (fun y : State N => liftR (τ i) (Vb i (y i))) x) := by sorry

end SmallGainISS.Lyapunov
