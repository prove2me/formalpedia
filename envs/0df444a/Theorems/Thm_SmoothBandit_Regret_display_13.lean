-- Prove2me | Theorems.Thm_SmoothBandit_Regret_display_13
-- name    : SmoothBandit.Regret.display_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:40.520134+00:00
-- url     : https://prove2.me/theorems/9d410c87-0079-4c9f-b708-586b2753bdec
-- title:
--   Display (13), first inequality, p. 23 — R_T(π̂) ≤ Σ_k γ2^{1+α}ϵ_{k−1}^{1+α}n_k + Σ_k n_k ℙ(Ḡ^C_{k−1} ∪ M̄^C_{k−1})
-- statement:
--   There is $T_0$, depending only on the parameters, such that for every horizon $T \ge T_0 \vee \exp\big(1 \vee \frac{C_0(2\beta+d)}{4(2r_0)^{2\beta}(2\beta+d+\beta d)}\big)$ and every instance of the class $\mathcal P$ (Assumptions 1 to 4), the regret of Algorithm 1 with horizon $T$ satisfies
--
--   $$R_T(\hat\pi) \le \sum_{k=1}^K \gamma\, 2^{1+\alpha}\epsilon_{k-1}^{1+\alpha} n_k + \sum_{k=1}^K n_k\, P\big(\bar{\mathcal G}^C_{k-1} \cup \bar{\mathcal M}^C_{k-1}\big),$$
--
--   where $K$ is the number of epochs, $n_k$ the epoch lengths (10), $\epsilon_k = 2^{-k}$ (so $\epsilon_0 = 1$), and $\bar{\mathcal G}_k$, $\bar{\mathcal M}_k$ the running intersections of the accuracy and sample-size events.
--
--   This decomposition reduces the regret bound to two tasks: the first sum is computed directly, and the probabilities in the second sum are bounded by Theorem 1.
--
--   **Formalization Note.** Only the first line of display (13) is formalized; the page's second line ("$\le = O(\cdot)$") is the computation finished in the proof of Theorem 2. The threshold on $T$ is Lemma 5's, on which the decomposition rests.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 23, display (13), first inequality (§4.1.2)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem display_13 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) :
    ∃ T0 : ℝ, ∀ T : ℕ,
      max T0 (Real.exp (max 1 (C0 P d * (2 * P.β + d) /
        (4 * (2 * P.r0) ^ (2 * P.β) * (2 * P.β + d + P.β * d))))) ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω), InClass P M →
        regret P M T ≤
          ∑ k ∈ Finset.Icc 1 (numEpochs P d T),
            P.γ * (2 : ℝ) ^ (1 + P.α) * eps (k - 1) ^ (1 + P.α) * (nEp P d T k : ℝ) +
          ∑ k ∈ Finset.Icc 1 (numEpochs P d T),
            (nEp P d T k : ℝ) *
              (M.P ((Gbar P T M (k - 1))ᶜ ∪ (Mbar P T M (k - 1))ᶜ)).toReal := by sorry

end SmoothBandit.Regret
