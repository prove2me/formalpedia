-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_1
-- name    : SKHessianAscent.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:01:49.553726+00:00
-- url     : https://prove2.me/theorems/24edfb6f-249d-4cea-a0dd-6518fc97d0c0
-- title:
--   Lemma 3.1 — Grönwall bound for the $L^2$ error of two synchronously coupled diffusions under local Lipschitzness
-- statement:
--   Let $S\subseteq U\subseteq\mathbb R^n$ be open with $U$ convex, and let $W$ be a standard Brownian motion in $\mathbb R^n$. Let $X$ solve $dX_t=f_t(X_t)\,dt+\Sigma_t(X_t)\,dW_t$ up to its exit from $U$, and let $\widehat X$ solve $d\widehat X_t=\widehat f_t(\widehat X_t)\,dt+\widehat\Sigma_t(\widehat X_t)\,dW_t$ up to its first exit time from $S$, both started at $0$ and driven by the same $W$. Write $S(r)=\{x\in U:B(x,r)\cap U\subseteq S\}$ and $S^2(r_1,r_2)=\{(x_1,x_2)\in U^2:x_1\in S(r_1),\|x_1-x_2\|_2<r_2\}$. Let $T\ge0$, $r>0$, $L_f,L_\Sigma>0$, and suppose that for $t\in[0,T]$:
--
--   1. $\mathbf E\big[\mathbf 1\{\tau(\widehat X)>t\}\|f_t(\widehat X_t)-\widehat f_t(\widehat X_t)\|_2^2\big]\le\varepsilon_f(t)^2$ and $\mathbf E\big[\mathbf 1\{\tau(X)>t\}\|\Sigma_t(X_t)-\widehat\Sigma_t(X_t)\|_F^2\big]\le\varepsilon_\Sigma(t)^2$, where $\tau(\cdot)$ is the exit time from $S$;
--   2. $f_t$ is $L_f$-segmentwise Lipschitz and $\widehat\Sigma_t$ is $L_\Sigma$-segmentwise Lipschitz on $S$ (in $\|\cdot\|_2$ and $\|\cdot\|_F$);
--   3. $\mathbf P\big(\forall s\le T,\ X_s\in S(r)\big)\ge1-\delta_1$.
--
--   Then for every $t\in[0,T]$,
--   $$\mathbf E\Big[\mathbf 1\{\forall s\le t,\ (X_s,\widehat X_s)\in S^2(r,r)\}\,\|X_t-\widehat X_t\|_2^2\Big]\le\int_0^t\Big(\frac{\sqrt2}{L_f}\varepsilon_f(s)^2+2\varepsilon_\Sigma(s)^2\Big)e^{(2\sqrt2L_f+2L_\Sigma^2)(t-s)}\,ds.$$
--   Moreover, if $1<r_2\le r$ and $t\le\frac{1}{2L_1}\log r_2$ with $L_1=2L_f+4L_\Sigma^2$, then
--   $$\mathbf P\big[\exists s\le t,\ (X_s,\widehat X_s)\notin S^2(r,r_2)\big]\le\delta_1+\frac{32tL_\Sigma^2+\int_0^t(32\varepsilon_\Sigma(s)^2+8\varepsilon_f(s))\,ds}{\log r_2}+\frac1{r_2}.$$
--
--   **Formalization Note** The paper does not define "segmentwise Lipschitz"; it is read as $\|g(x)-g(y)\|\le L\|x-y\|$ whenever the segment $[x,y]$ lies in $S$, and $U$ is assumed convex so that the segment from a point of $S(r)$ to a point of $U$ at distance $<r$ lies in $S$, as the proof uses. $L_1$ is not defined in the statement of the lemma; it is the constant $2L_b+4L_C^2$ of the proof of Lemma 3.2 with $L_b=L_f$, $L_C=L_\Sigma$, and the condition is written $2L_1t\le\log r_2$. The errors $\varepsilon_f,\varepsilon_\Sigma\ge0$ are assumed integrable on $[0,T]$ as needed for the right-hand sides. Both processes start at $0$; a common deterministic starting point reduces to this by translation.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.1, setup (3.3) and Lemma 3.1, pp. 8–9

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

theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (W : ℝ≥0 → Ω → SDEState n) (hW : IsStandardBrownian P W)
    (U S : Set (Fin n → ℝ)) (hU : IsOpen U) (hUc : Convex ℝ U) (hS : IsOpen S) (hSU : S ⊆ U)
    (f fh : ℝ≥0 → (Fin n → ℝ) → Fin n → ℝ)
    (Sg Sgh : ℝ≥0 → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (X Xh : ℝ≥0 → Ω → Fin n → ℝ)
    (hX : SolvesUntilExitT P W U f Sg X) (hXh : SolvesUntilExitT P W S fh Sgh Xh)
    (T : ℝ≥0) (r Lf LS δ₁ : ℝ) (hr : 0 < r) (hLf : 0 < Lf) (hLS : 0 < LS)
    (εf εS : ℝ → ℝ) (hεf : ∀ s, 0 ≤ εf s) (hεS : ∀ s, 0 ≤ εS s)
    (hεf_int : IntervalIntegrable εf volume 0 T)
    (hεf2_int : IntervalIntegrable (fun s => εf s ^ 2) volume 0 T)
    (hεS2_int : IntervalIntegrable (fun s => εS s ^ 2) volume 0 T)
    (h1f : ∀ t : ℝ≥0, t ≤ T →
      ∫⁻ ω in {ω | (t : ℝ≥0∞) < exitTime S fun s => Xh s ω},
        ENNReal.ofReal (l2 (f t (Xh t ω) - fh t (Xh t ω)) ^ 2) ∂P ≤ ENNReal.ofReal (εf t ^ 2))
    (h1S : ∀ t : ℝ≥0, t ≤ T →
      ∫⁻ ω in {ω | (t : ℝ≥0∞) < exitTime S fun s => X s ω},
        ENNReal.ofReal (frob (Sg t (X t ω) - Sgh t (X t ω)) ^ 2) ∂P ≤ ENNReal.ofReal (εS t ^ 2))
    (h2f : ∀ (t : ℝ≥0) (x y : Fin n → ℝ), segment ℝ x y ⊆ S →
      l2 (f t x - f t y) ≤ Lf * l2 (x - y))
    (h2S : ∀ (t : ℝ≥0) (x y : Fin n → ℝ), segment ℝ x y ⊆ S →
      frob (Sgh t x - Sgh t y) ≤ LS * l2 (x - y))
    (h3 : P {ω | ¬ ∀ s : ℝ≥0, s ≤ T → X s ω ∈ expandedSafe distVec U S r} ≤ ENNReal.ofReal δ₁) :
    (∀ t : ℝ≥0, t ≤ T →
      ∫⁻ ω in {ω | ∀ s : ℝ≥0, s ≤ t → (X s ω, Xh s ω) ∈ safePair distVec U S r r},
          ENNReal.ofReal (l2 (X t ω - Xh t ω) ^ 2) ∂P ≤
        ENNReal.ofReal (∫ s in (0 : ℝ)..t,
          (Real.sqrt 2 / Lf * εf s ^ 2 + 2 * εS s ^ 2) *
            Real.exp ((2 * Real.sqrt 2 * Lf + 2 * LS ^ 2) * ((t : ℝ) - s)))) ∧
    (∀ (r₂ : ℝ) (t : ℝ≥0), 1 < r₂ → r₂ ≤ r → t ≤ T →
      (t : ℝ) * (2 * (2 * Lf + 4 * LS ^ 2)) ≤ Real.log r₂ →
      P {ω | ¬ ∀ s : ℝ≥0, s ≤ t → (X s ω, Xh s ω) ∈ safePair distVec U S r r₂} ≤
        ENNReal.ofReal (δ₁ +
          (32 * t * LS ^ 2 + ∫ s in (0 : ℝ)..t, (32 * εS s ^ 2 + 8 * εf s)) / Real.log r₂ +
          1 / r₂)) := by sorry

end SKHessianAscent
