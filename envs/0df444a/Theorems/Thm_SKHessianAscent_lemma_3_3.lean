-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_3
-- name    : SKHessianAscent.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:03:39.690885+00:00
-- url     : https://prove2.me/theorems/84d2b02e-cb9d-45a6-9f55-5cdc30292e0a
-- title:
--   Lemma 3.3 — $O(1)$ error of the TAP-estimated magnetization $m^y_t$ along stochastic localization
-- statement:
--   Let $0<\beta<1$ and $T\ge0$. There are constants $\rho=\rho(\beta,T)>0$ and $c=c_{\mathrm{TAP}}(\beta,T)>0$, a function $C:[0,T]\to\mathbb R$, and a sequence $\eta_n\to0$ such that the following holds for every $n$. Let $A\sim\mathrm{GOE}(n)$, let $y_t=t\sigma+B_t$ be the stochastic localization process of $\mu_{\beta A}$ with true magnetization $m_t=\langle\sigma\rangle_{y_t}$, let $m^y_t$ be the SL-TAP process, and let $(\widehat m_t,\widehat y_t)$ be the PHD-TAP pair driven by the same Brownian motion. Then
--
--   - (d2a) holds with these constants: $\mathbf P\{\forall t\in[0,T],\ B_\square(m_t,\rho\sqrt n)\subseteq\mathcal S_{\beta,A}(c)\}\ge1-\eta_n$;
--   - for each $t\in[0,T]$, with
--   $$G_t=\Big\{\forall s\le t:\ \big((m_s,y_s),(\widehat m_s,\widehat y_s)\big)\in S^2\big(\rho\sqrt n,\ c\rho\sqrt n/2\big)\Big\},$$
--   where $S^2$ is the safe pair set in $(-1,1)^n\times\mathbb R^n$ for the safe set $\{(m,y):m\in\mathcal S_{\beta,A}(c)\}$,
--   $$\mathbf E\big[\mathbf 1_{G_t}\|m^y_t-m_t\|_2^2\big]\le C(t)\qquad\text{and}\qquad\mathbf P(G_t)\ge1-\eta_n.$$
--
--   **Formalization Note** The paper states the lemma under the hypothesis that (d1), (d2a), (d2b), (d3), (d4) hold up to time $T$; these are established for all $0<\beta<1$ in Theorem B.3, Theorem 4.2, Lemma 4.3 and Corollary 6.10, so the statement is given for $0<\beta<1$ without hypotheses, as it is used in the proof of Theorem 1.1. The constants $\rho$, $c$ are tied to (d2a) by the first clause. "$1-o_n(1)$" is an explicit sequence $\eta_n\to0$ that depends only on $\beta$ and $T$. The statement holds for every probability space carrying the data and every choice of the processes.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.1, Lemma 3.3, pp. 11–12

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Localization
import Definitions.Def_SKHessianAscent_Transport
import Definitions.Def_SKHessianAscent_Dynamics
import Definitions.Def_SKHessianAscent_TapLocalization

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_3_3 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℝ≥0) :
    ∃ (ρ c : ℝ) (Cfun : ℝ≥0 → ℝ) (η : ℕ → ℝ), 0 < ρ ∧ 0 < c ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : SLProcess β n P),
        P {ω | ¬ ∀ t : ℝ≥0, t ≤ T →
            cubeBall (X.mag t ω) (ρ * Real.sqrt n) ⊆ safeSet β (X.mat ω) c} ≤
          ENNReal.ofReal (η n) ∧
        ∀ M Mh Yh : ℝ≥0 → Ω → Fin n → ℝ, IsSLTAP P β c X.A X.y X.mag M →
          IsPHDTAP P β c X.A X.y X.mag Mh Yh →
          ∀ t : ℝ≥0, t ≤ T →
            let G : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ t →
              ((X.mag s ω, X.y s ω), (Mh s ω, Yh s ω)) ∈
                safePair distPair (cube n ×ˢ Set.univ)
                  {p | p.1 ∈ safeSet β (X.mat ω) c}
                  (ρ * Real.sqrt n) (c * ρ * Real.sqrt n / 2)}
            ∫⁻ ω in G, ENNReal.ofReal (l2 (M t ω - X.mag t ω) ^ 2) ∂P ≤
                ENNReal.ofReal (Cfun t) ∧
              P Gᶜ ≤ ENNReal.ofReal (η n) := by sorry

end SKHessianAscent
