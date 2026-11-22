-- Prove2me | Theorems.Thm_SKHessianAscent_corollary_3_15
-- name    : SKHessianAscent.corollary_3_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:09:51.819804+00:00
-- url     : https://prove2.me/theorems/fc4f5876-523e-4ff7-900f-27f2ac7403ab
-- title:
--   Corollary 3.15 — sub-Gaussian concentration of the Jarzynski weight $\widehat w_T$ on surviving ASL-TAP paths
-- statement:
--   For all $L,L_{\mathrm{drift}}>0$ there is a constant $K=K(L,L_{\mathrm{drift}})>0$ with the following property. Fix $0<\beta<1$, $c>0$ and a symmetric real $n\times n$ matrix $A$ with $\|A\|_{\mathrm{op}}\le3$; $D(m)=\mathrm{diag}(1/(1-m_i^2))$, $\widehat Q(m)=(\nabla^2_m\mathcal F_{\mathrm{TAP}}(m))^{-1}$, $f$ is the drift (2.4) and $\mathcal S_{\beta,A}(c)$ the safe set. Assume (d3), (d4) with constants $L$, $L_{\mathrm{drift}}$, (d5) with constant $L_\omega$ ($|\omega(m)-\omega(w)|\le L_\omega\|m-w\|_2$ on $\mathcal S_{\beta,A}(c)$), and $0_n\in\mathcal S_{\beta,A}(c)$. Stop the ASL-TAP-JE process at $\tau_c$ and set $S_T=\{\tau_c>T\}$. Then for every $0<T<\infty$ and $\lambda\in\mathbb R$,
--   $$\mathbf E_B\Big[\mathbf 1_{S_T}\,e^{\lambda(\widehat w_T-\mathbf E_B[\widehat w_T\mid S_T])}\Big]\le\exp\big(2\lambda^2c_{T_2}T^2L_\omega^2\big),\qquad c_{T_2}=3Tc^{-2}\exp\big(3T(T+4)K^2\big).\tag{3.10}$$
--   The left-hand side is zero by convention if $\mathbf P_B(S_T)=0$.
--
--   **Formalization Note** $c_{T_2}$ is "as in Theorem 3.13": the same expression in a constant $K$ that depends only on $L$ and $L_{\mathrm{drift}}$. $\mathbf E_B[\widehat w_T\mid S_T]$ is $\mathbf E[\widehat w_T\mathbf 1_{S_T}]/\mathbf P(S_T)$, and the integral over a null event is $0$, which is the stated convention.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.4, Corollary 3.15 and (3.10), pp. 16–17

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Transport
import Definitions.Def_SKHessianAscent_Dynamics

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem corollary_3_15 (L Ld : ℝ) (hL : 0 < L) (hLd : 0 < Ld) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (β c ε Lω T : ℝ) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
        0 < β → β < 1 → 0 < c → 0 < T → A.IsSymm → opNorm A ≤ 3 →
        (∀ m ∈ safeSet β A c, l2 (fDrift β A m - m) ≤ ε) →
        (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          frob (Qhat β A m - Qhat β A w) ≤ L * l2 (m - w)) →
        (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          l2 (aslDrift β A m - aslDrift β A w) ≤ Ld * l2 (m - w)) →
        (∀ m ∈ safeSet β A c, ∀ w ∈ safeSet β A c,
          |omega β A m - omega β A w| ≤ Lω * l2 (m - w)) →
        (0 : Fin n → ℝ) ∈ safeSet β A c →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (W : ℝ≥0 → Ω → SDEState n), IsStandardBrownian P W →
          ∀ M : ℝ≥0 → Ω → Fin n → ℝ, IsASLTAP P W β A c M →
            let τ : Ω → ℝ≥0∞ := fun ω => exitTime (safeSet β A c) fun s => M s ω
            let S : Set Ω := {ω | ENNReal.ofReal T < τ ω}
            let w : Ω → ℝ := jeWeight β A τ M T
            ∀ lam : ℝ,
              ∫⁻ ω in S, ENNReal.ofReal
                  (Real.exp (lam * (w ω - (∫ x in S, w x ∂P) / (P S).toReal))) ∂P ≤
                ENNReal.ofReal (Real.exp (2 * lam ^ 2 *
                  (3 * T * c ^ (-2 : ℤ) * Real.exp (3 * T * (T + 4) * K ^ 2)) *
                  T ^ 2 * Lω ^ 2)) := by sorry

end SKHessianAscent
