-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_inequality_2
-- name    : SecretaryPred.LearnedDynkin.inequality_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:44.443699+00:00
-- url     : https://prove2.me/theorems/bb0ac6fb-528b-4e67-9f4c-4be6919d836b
-- title:
--   Proof of Theorem 1, inequality (2), p. 9 (read with v(i∗)) — ı̂, i∗ ∉ M: v(ı̂) ≥ (1−θ)/(1+θ)·v(i∗)
-- statement:
--   Let $n$ candidates have values $v(i)\ge 0$ and predictions $\hat v(i)\ge 0$, let $\hat\imath$ be any maximizer of $\hat v$, let $i^*$ be the best candidate (largest value, ties broken by the smaller index), and let $\theta\ge 0$. If neither $\hat\imath$ nor $i^*$ deviates, i.e. $|1-\hat v(\hat\imath)/v(\hat\imath)|\le\theta$ and $|1-\hat v(i^*)/v(i^*)|\le\theta$, then
--
--   $$v(\hat\imath)\;\ge\;\frac{1}{1+\theta}\hat v(\hat\imath)\;\ge\;\frac{1}{1+\theta}\hat v(i^*)\;\ge\;\frac{1-\theta}{1+\theta}\,v(i^*).$$
--
--   This is inequality (2) in case (vi) of the proof of Theorem 1: when both $\hat\imath$ and $i^*$ are predicted accurately up to $\theta$, hiring $\hat\imath$ recovers a $(1-\theta)/(1+\theta)$ fraction of the optimum.
--
--   **Formalization Note** Candidates are `Fin n` (0-based); "does not deviate" is $|v(i)-\hat v(i)|\le\theta\,v(i)$.
--
--   Differences from the source:
--   - reading: the printed last term of (2) is (1 − θ)/(1 + θ)·v̂(i∗) → (1 − θ)/(1 + θ)·v(i∗); reason: the case's ratio is taken against v(i∗), so the proof uses the inequality with v(i∗); the analogue in §6.1 (p. 23) prints v(i∗); the printed chain is true but is not the inequality used
--   - generalization: θ = 0.646 → any θ ≥ 0; reason: the chain of (2) uses only 1 + θ > 0; at θ = 0.646 it is the source's inequality
--   - reading: line 8 of Algorithm 1: 'i is the best so far', with ties not addressed; i∗ ∈ argmax v → i beats every earlier arrival in the strict order 'larger value, then smaller index' (Beats); istar is the top candidate of that order; reason: both untied readings make Theorem 1 false: strictly larger value fails for n ≥ 5 candidates all with v = 1 and exact predictions except v̂(ı̂) = 10 (P(hire) ≤ 1/n < 0.215); weakly larger value fails for i∗ with v = v̂ = 1, ı̂ with v = δ, v̂ = 10 and n − 2 fillers with v = v̂ = δ (ratio → δ as n → ∞); for distinct values the order is the source's
--   - encoding: |1 − v̂(i)/v(i)| > θ (line 4 and the set M, p. 6) → θ·v(i) < |v(i) − v̂(i)| (Deviates); reason: identical when v(i) > 0; avoids Lean's x/0 = 0, and for v(i) = 0 a candidate deviates iff v̂(i) ≠ 0
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, p. 9, proof of Theorem 1, case (vi), inequality (2)

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem inequality_2 (n : ℕ) (theta : ℝ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j) (htheta : 0 ≤ theta)
    (hhatM : ¬ Deviates theta v vhat ihat) (hstarM : ¬ Deviates theta v vhat istar) :
    (1 - theta) / (1 + theta) * v istar ≤ v ihat := by sorry

end SecretaryPred.LearnedDynkin
