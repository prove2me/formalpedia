-- Prove2me | Theorems.Thm_SmoothBandit_Regret_lemma_3
-- name    : SmoothBandit.Regret.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:44.664696+00:00
-- url     : https://prove2.me/theorems/73f35b12-b529-449a-b97c-cfc89a2ffcd2
-- title:
--   Lemma 3 (second sentence), p. 18 — for β ≥ 1 there is T₀ > 0 with H_{±1,k} ≥ √d δ for 1 ≤ k ≤ K whenever T > T₀
-- statement:
--   Let $\beta \ge 1$. For an epoch $k$ of Algorithm 1 with horizon $T$, let $N_{\pm1,k}$ be the number of samples of arm $\pm1$ in epoch $k$ and $H_{\pm1,k} = N_{\pm1,k}^{-1/(2\beta+d)}$ the bandwidth built from them; let $\delta = T^{-\beta/(2\beta+d)}(\log T)^{-1}$ be the cube side. There is $T_0 > 0$, depending only on the parameters, such that for every $T > T_0$, on every sample path,
--
--   $$H_{\pm1,k} \ge \sqrt d\,\delta \qquad \text{for } 1 \le k \le K .$$
--
--   The bandwidth of the local polynomial estimates is therefore never smaller than the diameter of a cube: each estimate uses data from outside its own cube.
--
--   **Formalization Note.** $T_0$ is chosen before the instance and the sample path. $H$ uses $\max(N, 1)$ in place of $N$ (at $N = 0$ the page's $H$ is $+\infty$). The lemma's first display is not formalized: as printed it lacks the power $2\beta + d$ on its left side (the proof, pp. 43–44, bounds $(H_{\pm1,k}/(\sqrt d\delta))^{2\beta+d}$), and is false for $\beta > 1$.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 18, Lemma 3, second sentence (proof pp. 43–44)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem lemma_3 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℕ, T0 < T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω) (ω : Ω) (k : ℕ),
        1 ≤ k → k ≤ numEpochs P d T → ∀ a : Arm,
          Real.sqrt d * delta P d T ≤ Hk P T M a k ω := by sorry

end SmoothBandit.Regret
