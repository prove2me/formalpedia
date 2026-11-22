-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_7
-- name    : SKHessianAscent.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:05:23.886694+00:00
-- url     : https://prove2.me/theorems/390662f1-39bb-4f75-ab36-be4dea8855b4
-- title:
--   Lemma 3.7 — the TAP-estimated magnetization $m^y$ of the SL process survives in the safe set with probability $1-o_n(1)$
-- statement:
--   Let $0<\beta<1$ and $T\ge0$. There are $\rho=\rho(\beta,T)>0$, $c=c_{\mathrm{TAP}}(\beta,T)>0$ and a sequence $\eta_n\to0$ such that for every $n$, with $A\sim\mathrm{GOE}(n)$, $y_t$ the stochastic localization process of $\mu_{\beta A}$, $m_t=\langle\sigma\rangle_{y_t}$, and $m^y$ the SL-TAP process:
--
--   - (d2a) holds with these constants: $\mathbf P\{\forall t\in[0,T],\ B_\square(m_t,\rho\sqrt n)\subseteq\mathcal S_{\beta,A}(c)\}\ge1-\eta_n$;
--   - $\mathbf P\big[\exists t\le T,\ m^y_t\notin\mathcal S_{\beta,A}(c)\big]\le\eta_n$.
--
--   **Formalization Note** As for Lemma 3.3, the hypotheses "(d1), (d2a), (d2b), (d3), (d4) hold to time $T$" are theorems of the paper for $0<\beta<1$ and the statement is unconditional; the first clause ties $c$ to (d2a). The paper's conclusion "for all $t\in[0,T]$, $\mathbf P[m^y\notin S_t]=o_n(1)$" is the case $t=T$, which contains the others.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.2, Lemma 3.7, p. 14

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

theorem lemma_3_7 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℝ≥0) :
    ∃ (ρ c : ℝ) (η : ℕ → ℝ), 0 < ρ ∧ 0 < c ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : SLProcess β n P),
        P {ω | ¬ ∀ t : ℝ≥0, t ≤ T →
            cubeBall (X.mag t ω) (ρ * Real.sqrt n) ⊆ safeSet β (X.mat ω) c} ≤
          ENNReal.ofReal (η n) ∧
        ∀ M : ℝ≥0 → Ω → Fin n → ℝ, IsSLTAP P β c X.A X.y X.mag M →
          P {ω | ¬ ∀ t : ℝ≥0, t ≤ T → M t ω ∈ safeSet β (X.mat ω) c} ≤
            ENNReal.ofReal (η n) := by sorry

end SKHessianAscent
