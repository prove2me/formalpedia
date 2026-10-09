-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_u_eps_tendsto
-- name    : SLQSolv.OpenNotClosed.u_eps_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:21.285906+00:00
-- url     : https://prove2.me/theorems/05aa98d0-3d96-4aac-90f3-08ddddfed73a
-- title:
--   §7, p. 2306 — u_ε → −(x/(2 − 2t), x/(2 − 2t))ᵀ in L² as ε → 0
-- statement:
--   Let $t\in[0,1)$ and $x\in\mathbb R$, and let $u_\varepsilon=\Theta_\varepsilon X_\varepsilon$ be the closed-loop controls (7.10) of the regularized problems of Example 7.1. Then
--
--   $$
--   \lim_{\varepsilon\to0^+}\ \mathbb E\int_t^1\Big|u_\varepsilon(s)+\Big(\frac{x}{2-2t},\frac{x}{2-2t}\Big)^\top\Big|^2ds=0,
--   $$
--
--   that is, $u_\varepsilon\to-\big(\frac{x}{2-2t},\frac{x}{2-2t}\big)^\top$ in $L^2$ on $[t,1]$.
--
--   By Theorem 6.2 of the paper, this strong convergence is what makes the limit an open-loop optimal control.
--
--   **Formalization Note** $u_\varepsilon(s)=\Theta_\varepsilon(s)X_\varepsilon(s)$ with $\Theta_\varepsilon$ the feedback gain built from $P_\varepsilon(s)=\varepsilon/(\varepsilon+2-2s)$ and $X_\varepsilon$ the explicit state (7.9); the $L^2$ norm is the Euclidean one on $\mathbb R^2$.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 7.1, the display after (7.10), p. 2306

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- §7, p. 2306: for `t ∈ [0, 1)`, the closed-loop controls `u_ε = Θ_εX_ε` of (7.10) converge in
`L²` on `[t, 1]` to `−(x/(2 − 2t), x/(2 − 2t))ᵀ` as `ε → 0`. -/
theorem u_eps_tendsto {Ω : Type*} [MeasurableSpace Ω] (Bs : Basis Ω) (t : ℝ≥0) (ht : t < 1)
    (x : Fin 1 → ℝ) :
    let Pε : ℝ → ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ := fun ε s => !![ε / (ε + 2 - 2 * (s : ℝ))]
    let Xε : ℝ → ℝ≥0 → Ω → Fin 1 → ℝ := fun ε s _ =>
      ![((ε + 2 - 2 * ((max s t : ℝ≥0) : ℝ)) / (ε + 2 - 2 * (t : ℝ))) * x 0]
    let uε : ℝ → ℝ≥0 → Ω → Fin 2 → ℝ := fun ε s ω =>
      thetaOf ((ex71 (Ω := Ω)).addR ε) (Pε ε) s *ᵥ Xε ε s ω
    let ustar : ℝ≥0 → Ω → Fin 2 → ℝ := fun _ _ =>
      ![-(x 0) / (2 - 2 * (t : ℝ)), -(x 0) / (2 - 2 * (t : ℝ))]
    Tendsto (fun ε : ℝ => sqNorm Bs (ex71 (Ω := Ω)) t (fun s ω => uε ε s ω - ustar s ω))
      (𝓝[>] 0) (𝓝 0) := by sorry

end SLQSolv.OpenNotClosed
