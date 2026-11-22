-- Prove2me | Theorems.Thm_SKHessianAscent_corollary_B_1
-- name    : SKHessianAscent.corollary_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:23:01.242516+00:00
-- url     : https://prove2.me/theorems/99f5690c-24f3-4f76-850f-3f2073c37172
-- title:
--   Corollary B.1 — overlap and magnetization concentration for $\beta<1$ along stochastic localization
-- statement:
--   Let $0<\beta<1$, $T<\infty$ and let $k\ge1$ be an integer. There is a constant $C=C(\beta,k,T)$ and, for each $0\le t\le T$, a constant $c=c(\beta,k,t)>0$ such that the following holds for every $n$. Let $(m^*,q^*)\in[0,1)^2$ solve the fixed-point equations of [DLSS26a, Theorem 5.1] at time $t$, let $A\sim\mathrm{GOE}(n)$ and let $y_t=t\sigma^*+B_t$ be the stochastic localization of $\mu_{\beta A}$. With $\langle\cdot\rangle_t$ the average over independent replicas from the tilted measure $\mu_{\beta A,y_t}$, $R_{12}=\tfrac1n\langle\sigma^1,\sigma^2\rangle$ and $M=\tfrac1n\langle\sigma^1,\sigma^*\rangle$,
--   $$\mathbf E_{A,B_t}\big\langle(R_{12}-q^*)^{2k}\big\rangle_t\le\frac C{n^k}+Ce^{-cn},\qquad\mathbf E_{A,B_t}\big\langle(M-m^*)^{2k}\big\rangle_t\le\frac C{n^k}+Ce^{-cn}.$$
--
--   **Formalization Note** The paper writes the bounds as $\frac{C(k)}{n^k}+C(\beta,k)e^{-c(k,t)n}$. A constant $C(k)$ independent of $\beta$ is not possible: at $t=0$ and $k=1$, $n\,\mathbf E\langle R_{12}^2\rangle\to1/(1-\beta^2)$, which is unbounded as $\beta\to1$. The statement lets all constants depend on $\beta$, $k$ and the horizon, and $c$ on $t$. The magnetization $M$ is the overlap with the planted configuration, as in [DLSS26a, Theorem 5.2]; in the posterior form of the localization the planted configuration is the sample $\sigma^*$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Appendix B, Corollary B.1, p. 47

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Localization
import Definitions.Def_SKHessianAscent_Cavity

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem corollary_B_1 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℝ≥0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ T → ∃ c : ℝ, 0 < c ∧
      ∀ m q : ℝ, 0 ≤ m → m < 1 → 0 ≤ q → q < 1 → IsCavityFP β t m q →
        ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : SLProcess β n P),
          ∫⁻ ω, ENNReal.ofReal
              (∑ x : Spin n, ∑ z : Spin n,
                X.mu t ω x * X.mu t ω z * (overlap x z - q) ^ (2 * k)) ∂P ≤
            ENNReal.ofReal (C / (n : ℝ) ^ k + C * Real.exp (-c * n)) ∧
          ∫⁻ ω, ENNReal.ofReal
              (∑ x : Spin n, X.mu t ω x * (overlap x (X.σ ω) - m) ^ (2 * k)) ∂P ≤
            ENNReal.ofReal (C / (n : ℝ) ^ k + C * Real.exp (-c * n)) := by sorry

end SKHessianAscent
