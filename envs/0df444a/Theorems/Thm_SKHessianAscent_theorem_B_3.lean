-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_B_3
-- name    : SKHessianAscent.theorem_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T01:21:23.124804+00:00
-- url     : https://prove2.me/theorems/3af0e843-af5d-482a-acfe-dd0d79f01db3
-- title:
--   Theorem B.3, desideratum (d1) — $O(1)$ error of the TAP covariance estimate: $\mathbf E\|\nabla^2_m\mathcal F_{\mathrm{TAP}}(m_t)Q_t-I_n\|_F^2=O(1)$ for $\beta<1$
-- statement:
--   Fix $0<\beta<1$ and a time horizon $T\ge0$. Let $A\sim\mathrm{GOE}(n)$, let $(y_t)$ be stochastic localization of $\mu_{\beta A}$, $m_t=\langle\sigma\rangle_{y_t}$ and $Q_t=\mathrm{Cov}(\mu_{y_t})$. There is a constant $K=K(\beta,T)<\infty$, independent of $n$, such that for every $t\in[0,T]$
--
--   $$
--   \mathbf E_{A,B_t}\Big[\big\|\nabla^2_m\mathcal F_{\mathrm{TAP}}(m_t)\,Q_t-I_n\big\|_F^2\Big]\le K .
--   $$
--
--   Equivalently, the inverse of the TAP Hessian at the magnetization approximates the covariance of the localized Gibbs measure with $O(1)$ Frobenius error; this is the estimate that makes the TAP free energy a usable surrogate for the true free energy.
--
--   **Formalization Note** The paper writes the bound as $\varepsilon_{\mathrm{cov}}(\beta,t)^2$ with $\sup_{t\in[0,T]}\varepsilon_{\mathrm{cov}}(\beta,t)<\infty$, which is the single constant $K$. Its Theorem B.3 is phrased "assume overlap and magnetization concentration (Corollary B.1) and the spectral radius bound (Lemma B.2)"; both are proved in the paper for $0<\beta<1$ and are not hypotheses here. The process is an `SLProcess` (posterior form $y_t=t\sigma+B_t$) on an arbitrary probability space, and the expectation is a lower Lebesgue integral.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Theorem B.3, p. 48; desideratum (d1), p. 5

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Localization

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem theorem_B_3 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℝ≥0) :
    ∃ K : ℝ,
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : SLProcess β n P) (t : ℝ≥0),
        t ≤ T →
          ∫⁻ ω, ENNReal.ofReal
              (frob (tapHess β (X.mat ω) (X.mag t ω) * X.cov t ω - 1) ^ 2) ∂P ≤
            ENNReal.ofReal K := by sorry

end SKHessianAscent
