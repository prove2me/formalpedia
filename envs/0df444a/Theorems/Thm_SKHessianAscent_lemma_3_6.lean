-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_6
-- name    : SKHessianAscent.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:04:28.694802+00:00
-- url     : https://prove2.me/theorems/f324d59d-65c6-40f3-a0a8-1088465c2fce
-- title:
--   Lemma 3.6 — Jarzynski's equality with survival: the density of the SL-TAP path law against the ASL-TAP path law on surviving paths
-- statement:
--   Fix $\beta$, $c$, $T\ge0$ and a symmetric real $n\times n$ matrix $A$. Let $m^y$ be the SL-TAP process of the stochastic localization $y_t=t\sigma+B_t$ of $\mu_{\beta A}$, with exit time $\tau=\inf\{t:m^y_t\notin\mathcal S_{\beta,A}(c)\}$, and let $\widehat m$ be the ASL-TAP process (on a possibly different probability space), with exit time $\widehat\tau$ and Jarzynski weight $\widehat w_T=\int_0^T\omega(\widehat m_t)\,dt$. Let $P_T^s$ and $\widehat P_T^s$ be the path laws of $m^y_{[0,T]}$ and $\widehat m_{[0,T]}$ restricted to the survival events $\{\tau>T\}$ and $\{\widehat\tau>T\}$. Then $P^s_T\ll\widehat P^s_T$ with
--   $$\frac{dP^s_T}{d\widehat P^s_T}(m_{[0,T]})=e^{w_T}\cdot\frac{e^{-\mathcal F_{\mathrm{TAP}}(0,0)}}{e^{-\mathcal F_{\mathrm{TAP}}(m_T,\widehat y(m_T))}}\cdot e^{-\frac{nT}{2}}\cdot\frac{Z_{\beta A,\widehat y(m_T)}}{Z_{\beta A,0}}.$$
--   That is, for every Borel set $\Gamma$ of paths in $C^0([0,T],\mathbb R^n)$,
--   $$\mathbf P\big[m^y_{[0,T]}\in\Gamma,\ \tau>T\big]=\widehat{\mathbf E}\Big[\mathbf 1\{\widehat m_{[0,T]}\in\Gamma,\ \widehat\tau>T\}\ e^{\widehat w_T}\,\frac{e^{-\mathcal F_{\mathrm{TAP}}(0,0)}}{e^{-\mathcal F_{\mathrm{TAP}}(\widehat m_T,\widehat y(\widehat m_T))}}\,e^{-\frac{nT}{2}}\,\frac{Z_{\beta A,\widehat y(\widehat m_T)}}{Z_{\beta A,0}}\Big].$$
--
--   **Formalization Note** The identity of densities is stated in integrated form over an arbitrary Borel set of paths. The second identity of the lemma, for the time-$T$ marginal $dp^s_T/d\widehat p_T$, is the case $\Gamma=\{\gamma:\gamma_T\in B\}$ of this one. $\widehat y$ is the solution of (TAP).
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.2, Lemma 3.6, pp. 12–13

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

theorem lemma_3_6 (β c : ℝ) (T : ℝ≥0) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P']
    (Y : SLQuenched β A P) (M : ℝ≥0 → Ω → Fin n → ℝ)
    (hM : IsSLTAP P β c (fun _ i j => A i j) Y.y Y.mag M)
    (W : ℝ≥0 → Ω' → SDEState n) (hW : IsStandardBrownian P' W)
    (Mh : ℝ≥0 → Ω' → Fin n → ℝ) (hMh : IsASLTAP P' W β A c Mh)
    (Γ : Set (SKWeakPoincare.PathSpace T n)) (hΓ : MeasurableSet Γ) :
    let τ : Ω → ℝ≥0∞ := fun ω => exitTime (safeSet β A c) fun t => M t ω
    let τh : Ω' → ℝ≥0∞ := fun ω => exitTime (safeSet β A c) fun t => Mh t ω
    P {ω | pathOf T (fun t ω => WithLp.toLp 2 (M t ω)) ω ∈ Γ ∧ (T : ℝ≥0∞) < τ ω} =
      ∫⁻ ω in {ω | pathOf T (fun t ω => WithLp.toLp 2 (Mh t ω)) ω ∈ Γ ∧ (T : ℝ≥0∞) < τh ω},
        ENNReal.ofReal (
          Real.exp (jeWeight β A τh Mh T ω) *
          (Real.exp (-(FTAP β A 0 0)) /
            Real.exp (-(FTAP β A (Mh T ω) (yhat β A (Mh T ω))))) *
          Real.exp (-((n : ℝ) * T / 2)) *
          (partFn β A (yhat β A (Mh T ω)) / partFn β A 0)) ∂P' := by sorry

end SKHessianAscent
