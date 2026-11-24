-- Prove2me | Theorems.Thm_PINNGeneralization_heat_energy_estimate
-- name    : PINNGeneralization.heat_energy_estimate
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:47:05.965809+00:00
-- url     : https://prove2.me/theorems/213e7f0a-bf66-4a41-b50b-5eb79c8cbb5a
-- title:
--   Eq. (3.15) (as proved): stability estimate for the semilinear parabolic equation
-- statement:
--   Let $D\subseteq\mathbb R^d$ be open, connected and bounded with $C^k$ boundary, $k\ge2$, and let $T>0$. Let $f:\mathbb R\to\mathbb R$ satisfy $|f(v)-f(w)|\le C_f|v-w|$, let $\bar u\in C^k$, and let $u\in C^k(\bar D\times[0,T])$ be a classical solution of
--
--   $$u_t=\Delta u+f(u)\ \text{in }D\times(0,T),\qquad u(x,0)=\bar u(x)\ \text{in }D,\qquad u=0\ \text{on }\partial D\times(0,T).$$
--
--   Let $u^*$ be a neural network of $(x,t)$ with a $C^\infty$ activation function, with residuals $\mathcal R_{int},\mathcal R_{sb}=u^*|_{\partial D},\mathcal R_{tb}$. Then
--
--   $$\mathcal E_G^2\le\big(T+(1+2C_f)T^2e^{(1+2C_f)T}\big)\Big(\int_D\mathcal R_{tb}^2\,dx+\int_0^T\!\!\int_D\mathcal R_{int}^2\,dx\,dt+2\,C_{\partial D}(u,u^*)\,T^{1/2}\Big(\int_0^T\!\!\int_{\partial D}\mathcal R_{sb}^2\,ds\,dt\Big)^{1/2}\Big),$$
--
--   where $\mathcal E_G=(\int_0^T\int_D|u-u^*|^2)^{1/2}$ and $C_{\partial D}=|\partial D|^{1/2}(\|u\|_{C^1([0,T]\times\partial D)}+\|u^*\|_{C^1([0,T]\times\partial D)})$.
--
--   This is the PDE stability step of Theorem 3.1, before the quadrature bounds are applied.
--
--   **Formalization Note** The paper's (3.15) has $C_{\partial D}T^{1/2}$ without the factor $2$. Its energy inequality, multiplied by $2$ before the time integration, gives $2C_{\partial D}$. This statement gives what the proof establishes. $u\in C^k(\bar D\times[0,T])$ is written as the restriction of a $C^k$ function on $\mathbb R^d\times\mathbb R$.
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Section 3.3, proof of Theorem 3.1, eq. (3.15), p. 14

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory

namespace PINNGeneralization

theorem heat_energy_estimate {n k : ℕ} (hk : 2 ≤ k) (D : Set (Pt (n + 1)))
    (hD : IsCkDomain k D) (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (Cf : ℝ)
    (hf : ∀ v w, |f v - f w| ≤ Cf * |v - w|)
    (ubar : Pt (n + 1) → ℝ) (hubar : ContDiff ℝ k ubar)
    (u : Pt (n + 1) → ℝ → ℝ) (hu : ContDiff ℝ k (fun q : Pt (n + 1) × ℝ => u q.1 q.2))
    (hsol : IsHeatSolution D T f ubar u)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (ustar : Pt (n + 1) → ℝ → ℝ) (hustar : IsPINN σ ustar) :
    genErrorL2 D T u ustar ^ 2 ≤
      (T + (1 + 2 * Cf) * T ^ 2 * Real.exp ((1 + 2 * Cf) * T)) *
        ((∫ x in D, heatResTb ubar ustar x ^ 2) +
          (∫ t in Set.Ioo 0 T, ∫ x in D, heatResInt f ustar x t ^ 2) +
          2 * heatCbdry D T u ustar * Real.sqrt T *
            Real.sqrt (∫ q, ustar q.1 q.2 ^ 2 ∂bdryTimeMeasure D T)) := by sorry

end PINNGeneralization
