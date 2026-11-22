-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_2
-- name    : SKHessianAscent.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:02:46.169435+00:00
-- url     : https://prove2.me/theorems/02fd4069-1bf7-499a-a29f-35a9599005d7
-- title:
--   Lemma 3.2 — an approximate process stays within distance $r_2$ of an ideal process that stays in the expanded safe set
-- statement:
--   Let $S\subseteq U\subseteq\mathbb R^n$ be open, $W$ a standard Brownian motion in $\mathbb R^n$ with completed natural filtration, and $X,\widehat X$ continuous adapted processes with values in $U$. Let $1<r_2\le r$ and $\tau_2=\inf\{t\ge0:(X_t,\widehat X_t)\notin S^2(r,r)\}$. Suppose that $\Delta_t=X_t-\widehat X_t$ satisfies, up to $\tau_2$,
--   $$d\Delta_t=b_t\,dt+C_t\,dW_t,\qquad\Delta_0=0,$$
--   with $b_t=b^{\mathrm{Lip}}_t+b^{\mathrm{err}}_t$ and $C_t=C^{\mathrm{Lip}}_t+C^{\mathrm{err}}_t$ such that, when $(X_t,\widehat X_t)\in S^2(r,r)$,
--   $$\|b^{\mathrm{Lip}}_t\|_2\le L_b\|\Delta_t\|_2,\qquad\|C^{\mathrm{Lip}}_t\|_F\le L_C\|\Delta_t\|_2,$$
--   and for $s\le t$,
--   $$\mathbf E\big[\mathbf 1\{s<\tau_2\}\|b^{\mathrm{err}}_s\|_2^2\big]\le\varepsilon_b(s)^2,\qquad\mathbf E\big[\mathbf 1\{s<\tau_2\}\|C^{\mathrm{err}}_s\|_F^2\big]\le\varepsilon_C(s)^2.$$
--   Suppose $\mathbf P(\exists s\le t,\ X_s\notin S(r))\le\delta_1$ and $t\le\frac{1}{2L_1}\log r_2$, where $L_1=2L_b+4L_C^2$. Then
--   $$\mathbf P\big[\exists s\le t,\ (X_s,\widehat X_s)\notin S^2(r,r_2)\big]\le\delta_1+\frac{32tL_C^2+\int_0^t(32\varepsilon_C(s)^2+8\varepsilon_b(s))\,ds}{\log r_2}+\frac1{r_2}.$$
--
--   **Formalization Note** The paper's statement reads "if $r\le r_2$"; the definition of $S^2(r_1,r_2)$ requires $r_1\ge r_2$, Lemma 3.1 has "$r_2\le r$", and the proof uses $r_2^2\le r^2$, so the condition is $r_2\le r$; $r_2>1$ makes $\log r_2>0$. $L_1=2L_b+4L_C^2$ is the constant defined in the proof, and the time condition is written $2L_1t\le\log r_2$. "$d\Delta_t=b_t\,dt+C_t\,dW_t$ up to $\tau_2$" is the statement that the stopped process $\Delta_{t\wedge\tau_2}$ equals $\int_0^t\mathbf 1\{s<\tau_2\}b_s\,ds+\int_0^t\mathbf 1\{s<\tau_2\}C_s\,dW_s$. The function $32\varepsilon_C^2+8\varepsilon_b$ is assumed integrable on $[0,t]$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.1, Lemma 3.2, pp. 9–11

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

theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (W : ℝ≥0 → Ω → SDEState n) (hW : IsStandardBrownian P W)
    (U S : Set (Fin n → ℝ)) (hU : IsOpen U) (hS : IsOpen S) (hSU : S ⊆ U)
    (X Xh : ℝ≥0 → Ω → Fin n → ℝ) (hXU : ∀ t ω, X t ω ∈ U) (hXhU : ∀ t ω, Xh t ω ∈ U)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXhc : ∀ ω, Continuous fun t => Xh t ω)
    (hXm : ∀ t, Measurable[completedBrownianPast P W (fun _ => 0) t] (X t))
    (hXhm : ∀ t, Measurable[completedBrownianPast P W (fun _ => 0) t] (Xh t))
    (r r₂ Lb LC δ₁ : ℝ) (t : ℝ≥0) (hr₂ : 1 < r₂) (hr : r₂ ≤ r) (hLb : 0 ≤ Lb) (hLC : 0 ≤ LC)
    (εb εC : ℝ → ℝ) (hεb : ∀ s, 0 ≤ εb s)
    (hεint : IntervalIntegrable (fun s => 32 * εC s ^ 2 + 8 * εb s) volume 0 t)
    (bL bE : ℝ≥0 → Ω → Fin n → ℝ) (CL CE : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hΔ : IsItoStopped P (completedBrownianPast P W fun _ => 0) W
      (fun ω => exitTime (safePair distVec U S r r) fun s => (X s ω, Xh s ω))
      (fun s ω => bL s ω + bE s ω) (fun s ω => CL s ω + CE s ω)
      (stopAt (fun ω => exitTime (safePair distVec U S r r) fun s => (X s ω, Xh s ω))
        fun s ω => X s ω - Xh s ω))
    (hbL : ∀ s ω, (X s ω, Xh s ω) ∈ safePair distVec U S r r →
      l2 (bL s ω) ≤ Lb * l2 (X s ω - Xh s ω))
    (hCL : ∀ s ω, (X s ω, Xh s ω) ∈ safePair distVec U S r r →
      frob (CL s ω) ≤ LC * l2 (X s ω - Xh s ω))
    (hbE : ∀ s : ℝ≥0, s ≤ t →
      ∫⁻ ω in {ω | (s : ℝ≥0∞) < exitTime (safePair distVec U S r r) fun u => (X u ω, Xh u ω)},
        ENNReal.ofReal (l2 (bE s ω) ^ 2) ∂P ≤ ENNReal.ofReal (εb s ^ 2))
    (hCE : ∀ s : ℝ≥0, s ≤ t →
      ∫⁻ ω in {ω | (s : ℝ≥0∞) < exitTime (safePair distVec U S r r) fun u => (X u ω, Xh u ω)},
        ENNReal.ofReal (frob (CE s ω) ^ 2) ∂P ≤ ENNReal.ofReal (εC s ^ 2))
    (hδ₁ : P {ω | ¬ ∀ s : ℝ≥0, s ≤ t → X s ω ∈ expandedSafe distVec U S r} ≤ ENNReal.ofReal δ₁)
    (ht : (t : ℝ) * (2 * (2 * Lb + 4 * LC ^ 2)) ≤ Real.log r₂) :
    P {ω | ¬ ∀ s : ℝ≥0, s ≤ t → (X s ω, Xh s ω) ∈ safePair distVec U S r r₂} ≤
      ENNReal.ofReal (δ₁ +
        (32 * t * LC ^ 2 + ∫ s in (0 : ℝ)..t, (32 * εC s ^ 2 + 8 * εb s)) / Real.log r₂ +
        1 / r₂) := by sorry

end SKHessianAscent
