-- Prove2me | Theorems.Thm_PINNGeneralization_vscl_energy_estimate
-- name    : PINNGeneralization.vscl_energy_estimate
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:48:05.704931+00:00
-- url     : https://prove2.me/theorems/85eb94e5-6a1a-4395-9a22-906e6f460efc
-- title:
--   Eq. (4.18) (as proved): stability estimate for the viscous scalar conservation law
-- statement:
--   Let $\nu>0$, $T>0$, $k\ge2$, $f,\bar u\in C^k(\mathbb R)$, and let $u\in C^k([0,1]\times[0,T])$ be a classical solution of
--
--   $$u_t+f(u)_x=\nu u_{xx}\ \text{in }(0,1)\times(0,T),\qquad u(x,0)=\bar u(x),\qquad u(0,t)=u(1,t)=0.$$
--
--   Let $u^*$ be a neural network of $(x,t)$ with a $C^\infty$ activation, with residuals $\mathcal R_{int},\mathcal R_{sb,0}=u^*(0,\cdot),\mathcal R_{sb,1}=u^*(1,\cdot),\mathcal R_{tb}$. Let $\mathbf C=1+2C_{f,u,u^*}$. Then
--
--   $$\mathcal E_G^2\le\big(T+\mathbf CT^2e^{\mathbf CT}\big)\,\mathcal C,$$
--
--   where
--
--   $$\mathcal C=\int_0^1\mathcal R_{tb}^2\,dx+\int_0^T\!\!\int_0^1\mathcal R_{int}^2\,dx\,dt+2\bar{\mathbf C}_b\Big[\int_0^T\mathcal R_{sb,0}^2\,dt+\int_0^T\mathcal R_{sb,1}^2\,dt\Big]+2\nu\mathbf C_bT^{1/2}\Big[\Big(\int_0^T\mathcal R_{sb,0}^2\Big)^{1/2}+\Big(\int_0^T\mathcal R_{sb,1}^2\Big)^{1/2}\Big],$$
--
--   with $C_{f,u,u^*}=\max_{|s|\le M}|f''(s)|\,\|u_x\|_\infty$, $M=\max(\|u\|_\infty,\|u^*\|_\infty)$, $\mathbf C_b=\|u_x\|_\infty+\|u^*_x\|_\infty$ and $\bar{\mathbf C}_b=\max_{|s|\le\|u^*\|_\infty}|f'(s)|$, all sup norms over $[0,1]\times[0,T]$.
--
--   This is the stability step of Theorem 4.1, obtained from the relative-entropy identity (4.13) and Grönwall's inequality.
--
--   **Formalization Note** The paper writes $C_{f,u,u^*}=|f''(\max\{\|u\|_\infty,\|u^*\|_\infty\})|\,\|u_x\|_\infty$. Its proof, through the Taylor remainder (4.14), needs $f''$ at intermediate points, so the maximum of $|f''|$ over $[-M,M]$ is used. The paper leaves $\bar{\mathbf C}_b$ as an unspecified function of $\|f'\|_\infty$ and $\|u^*\|_{C^0}$. The value used is the one its boundary computation produces. The hypothesis $u\in C^k((0,T)\times(0,1))$ is read as $u\in C^k([0,1]\times[0,T])$, as the boundary values and the constants require. It is written as the restriction of a $C^k$ function on $\mathbb R^2$.
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Section 4.3, proof of Theorem 4.1, eqs. (4.16)-(4.18), pp. 22-23

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory

namespace PINNGeneralization

theorem vscl_energy_estimate {k : ℕ} (hk : 2 ≤ k) (T ν : ℝ) (hT : 0 < T) (hν : 0 < ν)
    (f : ℝ → ℝ) (hf : ContDiff ℝ k f) (ubar : ℝ → ℝ) (hubar : ContDiff ℝ k ubar)
    (u : ℝ → ℝ → ℝ) (hu : ContDiff ℝ k (fun q : ℝ × ℝ => u q.1 q.2))
    (hsol : IsVSCLSolution T ν f ubar u)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (ustar : ℝ → ℝ → ℝ) (hustar : IsPINN1D σ ustar) :
    genErrorL2 (Set.Ioo 0 1) T u ustar ^ 2 ≤
      (T + (1 + 2 * vsclCf T f u ustar) * T ^ 2 * Real.exp ((1 + 2 * vsclCf T f u ustar) * T)) *
        ((∫ x in Set.Ioo 0 1, vsclResTb ubar ustar x ^ 2) +
          (∫ t in Set.Ioo 0 T, ∫ x in Set.Ioo 0 1, vsclResInt ν f ustar x t ^ 2) +
          2 * vsclCbarb T f ustar *
            ((∫ t in Set.Ioo 0 T, ustar 0 t ^ 2) + (∫ t in Set.Ioo 0 T, ustar 1 t ^ 2)) +
          2 * ν * vsclCb T u ustar * Real.sqrt T *
            (Real.sqrt (∫ t in Set.Ioo 0 T, ustar 0 t ^ 2) +
              Real.sqrt (∫ t in Set.Ioo 0 T, ustar 1 t ^ 2))) := by sorry

end PINNGeneralization
