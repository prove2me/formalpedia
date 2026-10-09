-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_eq_7_10
-- name    : SLQSolv.OpenNotClosed.eq_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:11.796792+00:00
-- url     : https://prove2.me/theorems/88c1554c-c7fe-43d5-9b41-489f84ef226d
-- title:
--   (7.9)–(7.10), p. 2306 — the closed-loop state X_ε and control u_ε = Θ_εX_ε of the regularized problem
-- statement:
--   Let $\varepsilon>0$, $t\in[0,1)$ and $x\in\mathbb R$, and let $P_\varepsilon(s)=\varepsilon/(\varepsilon+2-2s)$ be the solution (7.6). Set
--
--   $$
--   \Theta_\varepsilon\triangleq-\big(R+\varepsilon I+D^\top P_\varepsilon D\big)^{-1}\big(B^\top P_\varepsilon+D^\top P_\varepsilon C+S\big).
--   $$
--
--   Then:
--
--   1. $\Theta_\varepsilon(s)=-\dfrac{P_\varepsilon(s)}{\varepsilon}\begin{pmatrix}1\\1\end{pmatrix}$ for $s\in[0,1]$;
--   2. the closed-loop system $dX_\varepsilon=[A+B\Theta_\varepsilon]X_\varepsilon ds+[C+D\Theta_\varepsilon]X_\varepsilon dW=-\frac{2P_\varepsilon}{\varepsilon}X_\varepsilon ds$, $X_\varepsilon(t)=x$, has the solution (7.9)
--   $$
--   X_\varepsilon(s)=x\exp\Big\{-\int_t^s\frac{2P_\varepsilon(r)}{\varepsilon}dr\Big\}=\frac{\varepsilon+2-2s}{\varepsilon+2-2t}\,x,\qquad t\le s\le 1,
--   $$
--   and every solution agrees with it almost surely at each time $s\le 1$;
--   3. the closed-loop control is (7.10)
--   $$
--   u_\varepsilon(s)\triangleq\Theta_\varepsilon(s)X_\varepsilon(s)=-\Big(\frac{x}{\varepsilon+2-2t},\frac{x}{\varepsilon+2-2t}\Big)^\top,\qquad t\le s\le 1.
--   $$
--
--   These controls are the minimizing sequence whose $L^2$ limit is the open-loop optimal control (7.11) of Example 7.1.
--
--   **Formalization Note** The state is encoded on $[0,1]$ with $X_\varepsilon=x$ on $[0,t]$ (coefficients switched on at time $t$), which is why $X_\varepsilon$ is written with $\max(s,t)$. The closed-loop system uses $v_\varepsilon=0$, the second component of the closed-loop strategy for Problem (SLQ)$^0_\varepsilon$; the state equation does not involve $R$, so it is the state equation (7.1). The identity for $\Theta_\varepsilon$ is claimed on $[0,1]$ only: beyond $1$ the matrix $R+\varepsilon I+D^\top P_\varepsilon D$ may be singular.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 7.1, Θ_ε, (7.9)–(7.10), p. 2306

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- (7.9)–(7.10), p. 2306: for `ε > 0` and `(t, x) ∈ [0, 1) × ℝ`, the feedback
`Θ_ε = −(R + εI + DᵀP_εD)⁻¹(BᵀP_ε + DᵀP_εC + S)` equals `−(P_ε/ε)(1, 1)ᵀ` on `[0, 1]`; the closed-loop
system of `(Θ_ε, 0)` from `(t, x)` has the unique solution `X_ε(s) = (ε + 2 − 2s)/(ε + 2 − 2t) · x`
(`x` before `t`), and `u_ε = Θ_εX_ε = −(x/(ε + 2 − 2t), x/(ε + 2 − 2t))ᵀ` on `[t, 1]`. -/
theorem eq_7_10 {Ω : Type*} [MeasurableSpace Ω] (Bs : Basis Ω) (ε : ℝ) (hε : 0 < ε)
    (t : ℝ≥0) (ht : t < 1) (x : Fin 1 → ℝ) :
    let Pε : ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ := fun s => !![ε / (ε + 2 - 2 * (s : ℝ))]
    let Θε : ℝ≥0 → Matrix (Fin 2) (Fin 1) ℝ := thetaOf ((ex71 (Ω := Ω)).addR ε) Pε
    let Xε : ℝ≥0 → Ω → Fin 1 → ℝ := fun s _ =>
      ![((ε + 2 - 2 * ((max s t : ℝ≥0) : ℝ)) / (ε + 2 - 2 * (t : ℝ))) * x 0]
    (∀ s, s ≤ 1 → Θε s = -(Pε s 0 0 / ε) • !![1; 1]) ∧
    IsClosedLoopState Bs (ex71 (Ω := Ω)) t Θε 0 x Xε ∧
    (∀ X, IsClosedLoopState Bs (ex71 (Ω := Ω)) t Θε 0 x X →
      ∀ s, s ≤ 1 → ∀ᵐ ω ∂Bs.P, X s ω = Xε s ω) ∧
    ∀ s, t ≤ s → s ≤ 1 → ∀ ω, Θε s *ᵥ Xε s ω
      = ![-(x 0) / (ε + 2 - 2 * (t : ℝ)), -(x 0) / (ε + 2 - 2 * (t : ℝ))] := by sorry

end SLQSolv.OpenNotClosed
