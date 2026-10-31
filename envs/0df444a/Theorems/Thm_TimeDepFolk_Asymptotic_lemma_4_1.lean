-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_1
-- name    : TimeDepFolk.Asymptotic.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:13.688705+00:00
-- url     : https://prove2.me/theorems/681dea86-d052-4bbf-b5b5-b27900197c6e
-- title:
--   Lemma 4.1, p. 14 — patience is equivalent to uniform convergence of block ratios to (T₁+1)/(T₂+1)
-- statement:
--   Let $(\theta^k)_{k\ge1}$ be a sequence of evaluations. Then $(\theta^k)$ is patient if and only if, for all fixed integers $0\le T_1\le T_2$,
--   $$\lim_{k\to\infty}\frac{\sum_{t=T}^{T+T_1}\theta^k_t}{\sum_{t=T}^{T+T_2}\theta^k_t}=\frac{T_1+1}{T_2+1}\qquad\text{uniformly in } T\ge1 .$$
--
--   Patience says that consecutive weights become nearly equal; the lemma upgrades this to blocks of any fixed length, which is how the proof compares the weight of a punishment phase with the weight of the remaining game.
--
--   **Formalization Note.** Stages are 0-based, so $T$ ranges over $\mathbb N$ and $\theta^k_t$ is `(θ k).θ t`; the blocks are `Finset.Icc T (T + T₁)` and `Finset.Icc T (T + T₂)`. A ratio with a zero denominator is $0$ in Lean, which is never close to $(T_1+1)/(T_2+1)>0$, so both sides force the weights to be positive for large $k$.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 14, Lemma 4.1

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem lemma_4_1 (θ : ℕ → Evaluation) :
    IsPatient θ ↔ ∀ T1 T2 : ℕ, T1 ≤ T2 →
      TendstoUniformly
        (fun k T => (∑ t ∈ Finset.Icc T (T + T1), (θ k).θ t) /
          ∑ t ∈ Finset.Icc T (T + T2), (θ k).θ t)
        (fun _ => ((T1 : ℝ) + 1) / ((T2 : ℝ) + 1)) Filter.atTop := by sorry

end TimeDepFolk.Asymptotic
