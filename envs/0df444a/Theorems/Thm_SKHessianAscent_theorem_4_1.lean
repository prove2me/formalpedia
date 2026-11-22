-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_4_1
-- name    : SKHessianAscent.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:10:47.419806+00:00
-- url     : https://prove2.me/theorems/83d8e82c-db71-4064-8fb4-d906a0113b38
-- title:
--   Theorem 4.1 — "hybrid" local strong convexity: the planted TAP Hessian is $\succeq c_0$ on an $\varepsilon\sqrt n$-ball around a late AMP iterate
-- statement:
--   Let $0<\beta<1$ and $t>0$. There exist $c_0(\beta,t),c_1(\beta,t)>0$ such that for all $0<\varepsilon<c_1(\beta,t)$ and all $k\ge k_0(\varepsilon,\beta,t)$,
--   $$\mathbf P_{A,g_0}\Big\{\inf_{\sigma\in B_\square(m_{k-1},\varepsilon\sqrt n)}\nabla^2\mathcal F_{\mathrm{TAP}}(\sigma,\cdot)\succeq c_0(\beta,t)\Big\}\ge1-o_n(1).$$
--   Here $A\sim\mathrm{GOE}(n)$, $x_0\in\{\pm1\}^n$ is the planted configuration, $y_t=tx_0+\sqrt t\,g_0$ with $g_0\sim N(0,I_n)$, the AMP iterates are $m_{-1}=0_n$, $m_j=\tanh(z_j)$, $z_{j+1}=\beta(A+\tfrac\beta nx_0x_0^{\mathsf T})m_j+y_t-\beta^2(1-\|m_j\|_2^2/n)m_{j-1}$, and
--   $$\nabla^2\mathcal F_{\mathrm{TAP}}(m,\cdot)=\beta^2\Big(1-\frac{\|m\|_2^2}{n}\Big)I_n-\beta A+D(m)-\frac{\beta^2}nx_0x_0^{\mathsf T}-\frac{2\beta^2}nmm^{\mathsf T}$$
--   is the TAP Hessian of the SL-tilted planted model.
--
--   **Formalization Note** The paper states the theorem "for every $\beta,t>0$"; the section and the cited theorem of Celentano are for $0<\beta<1$, which is assumed. The paper writes $y_t=tx_0+g_0$; the tilt of the localization at time $t$ is $tx_0+B_t$ with $B_t\sim N(0,tI_n)$, as in the paper's own $Y^*=t_\infty+G+\sqrt tG_0$, so $y_t=tx_0+\sqrt tg_0$. $z_0=0_n$ as in [AMS22, Algorithm 1]. The statement is for every planted $x_0$ (the paper fixes $x_0=1_n$ by gauge symmetry), with $o_n(1)$ an explicit sequence depending on $\beta,t,\varepsilon,k$ only.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §4.1, Theorem 4.1, p. 20 (Celentano, syntactic modification of the proof of Theorem 2)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Localization
import Definitions.Def_SKHessianAscent_Cavity

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem theorem_4_1 (β t : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (ht : 0 < t) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ ε : ℝ, 0 < ε → ε < c₁ →
        ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 1 ≤ k →
          ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
            ∀ (n : ℕ) (x₀ : Spin n),
              ((RandMatDisc.goe n).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))
                  {p | ¬ ∀ u ∈ cubeBall
                      (ampMag β (planted β (Matrix.of p.1) x₀)
                        (fun i => t * spinValue (x₀ i) + Real.sqrt t * p.2 i) (k - 1))
                      (ε * Real.sqrt n),
                    (tapHess β (planted β (Matrix.of p.1) x₀) u -
                      c₀ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
                ENNReal.ofReal (η n) := by sorry

end SKHessianAscent
