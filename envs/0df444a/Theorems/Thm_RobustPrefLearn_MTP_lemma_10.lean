-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_10
-- name    : RobustPrefLearn.MTP.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:56.2857+00:00
-- url     : https://prove2.me/theorems/24433cff-cb14-42f4-acd0-522a9919d856
-- title:
--   Lemma 10, p. 72 — MTP's error probability is at most C̃_1 e^{−β}, with C̃_1 depending only on K
-- statement:
--   Let $K\ge2$. There is a constant $\tilde C_1$, depending only on $K$, such that for every $p\in(0,1)$, every initial display set $S_1$, every threshold $\beta>0$ and every preference $f\in\mathcal M_p$, the Myopic Tracking Policy satisfies
--   $$\mathbb P_f\bigl(d_\tau\neq\sigma_f^{-1}(1)\bigr)\le\tilde C_1e^{-\beta}.$$
--
--   The proof takes $\tilde C_1=|\overline\Sigma(\sigma_f)|=(K-1)(K-1)!$. This is the error estimate behind the accuracy of MTP (Theorem 7).
--
--   **Formalization Note** The constant is quantified after $K$ and before $p$, $S_1$, $\beta$ and $f$. The probability is $\mathbb P_f(\tau<\infty,\ d_\tau\ne\sigma_f^{-1}(1))$. $\beta>0$ is Algorithm 1's input condition. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 72, Lemma 10, (57)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Lemma 10, p. 72. There is a constant `C̃₁`, depending only on `K`, such that for every `p`,
every initial display set `S₁`, every threshold `β > 0` and every `f ∈ M_p`, the Myopic Tracking
Policy satisfies `P_f(d_τ ≠ σ_f^{-1}(1)) ≤ C̃₁ e^{-β}`. -/
theorem lemma_10 (K : ℕ) [NeZero K] (hK : 2 ≤ K) :
    ∃ C : ℝ, ∀ p : ℝ, 0 < p → p < 1 → ∀ (S1 : DS K) (β : ℝ), 0 < β →
      ∀ f ∈ (Mp p : Set (Pref K)),
        probWrong (mtp p S1 β) f ≤ ENNReal.ofReal (C * Real.exp (-β)) := by sorry

end RobustPrefLearn.MTP
