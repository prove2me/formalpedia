-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_case_ii
-- name    : SecretaryPred.LearnedDynkin.case_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:24.34379+00:00
-- url     : https://prove2.me/theorems/52b6a622-2d87-47ec-9dac-bf5b2113d86c
-- title:
--   Proof of Theorem 1, case (ii), pp. 7–8 — ı̂ = i∗ ∉ M: i∗ is hired with probability ≥ 1/(m+1) + τ Σ (m k)(−1)^(k−1)(1−τ^k)/k
-- statement:
--   Let $n$ candidates have values $v(i)\ge 0$ and predictions $\hat v(i)\ge 0$, let $\hat\imath$ be any maximizer of $\hat v$, and let $i^*$ be the best candidate (largest value, ties broken by the smaller index). Run Algorithm 1 (learned Dynkin) with threshold $\theta\ge 0$ and time $\tau\in(0,1)$ on independent Uniform$[0,1]$ arrival times. $M$ is the set of candidates with $|1-\hat v(i)/v(i)|>\theta$ and $m=|M|$.
--
--   **Case (ii).** Suppose $M\neq\emptyset$, $\hat\imath=i^*$ and $i^*\notin M$. Then
--
--   $$\Pr[\text{the algorithm hires } i^*]\;\ge\;\frac{1}{m+1}+\tau\sum_{k=1}^{m}\binom{m}{k}(-1)^{k-1}\frac{1-\tau^k}{k}.$$
--
--   The first term is the probability that $\hat\imath$ precedes every candidate of $M$ (and is hired in Prediction mode); the second is the closed form of $\int_\tau^1\{1-(1-t^*)^m\}\,\tau/t^*\,dt^*$, the Secretary-mode contribution.
--
--   **Formalization Note** Candidates are `Fin n` (0-based). The probability that $i^*$ is hired is `(arrivalLaw n).real {t | Hired θ τ v v̂ ı̂ t i∗}`, the measure of the set of arrival vectors on which Algorithm 1 hires $i^*$, under the uniform law on $[0,1]^n$. The case hypotheses are stated with the division-free deviation predicate `Deviates`, $i^*$ is the top candidate of the tie-broken order `Beats`, and $\hat\imath$ is any maximizer of $\hat v$.
--
--   Differences from the source:
--   - generalization: θ = 0.646, τ = 0.313 (Theorem 1) → any θ ≥ 0 and τ with 0 < τ < 1; reason: the case derivations never use the values of θ and τ (the paper evaluates the six case bounds on a grid of (θ, τ), p. 10); at θ = 0.646, τ = 0.313 the item is the source's step
--   - reading: line 8 of Algorithm 1: 'i is the best so far', with ties not addressed; i∗ ∈ argmax v → i beats every earlier arrival in the strict order 'larger value, then smaller index' (Beats); istar is the top candidate of that order; reason: both untied readings make Theorem 1 false: strictly larger value fails for n ≥ 5 candidates all with v = 1 and exact predictions except v̂(ı̂) = 10 (P(hire) ≤ 1/n < 0.215); weakly larger value fails for i∗ with v = v̂ = 1, ı̂ with v = δ, v̂ = 10 and n − 2 fillers with v = v̂ = δ (ratio → δ as n → ∞); for distinct values the order is the source's
--   - encoding: |1 − v̂(i)/v(i)| > θ (line 4 and the set M, p. 6) → θ·v(i) < |v(i) − v̂(i)| (Deviates); reason: identical when v(i) > 0; avoids Lean's x/0 = 0, and for v(i) = 0 a candidate deviates iff v̂(i) ≠ 0
--   - encoding: candidates N = [n] interviewed in random order, arrival times iid Uniform[0, 1] (§2.1), exactly one hire → candidates Fin n (0-based), t uniform on the cube [0, 1]^n (arrivalLaw n), the mode at i is Secretary iff some deviating j has t_j ≤ t_i, and algValue sums the values of all candidates that are first to stop; reason: the run differs from the source's single-hire run only on the null set of arrival vectors with two equal times
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, pp. 7–8, proof of Theorem 1, case (ii)

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem case_ii (n : ℕ) (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j)
    (htheta : 0 ≤ theta) (htau0 : 0 < tau) (htau1 : tau < 1)
    (hcase : ihat = istar) (hstarM : ¬ Deviates theta v vhat istar)
    (hMne : (Mset theta v vhat).Nonempty) (m : ℕ) (hm : (Mset theta v vhat).card = m) :
    1 / ((m : ℝ) + 1) +
        tau * ∑ k ∈ Finset.Icc 1 m,
          (m.choose k : ℝ) * (-1 : ℝ) ^ (k - 1) * (1 - tau ^ k) / (k : ℝ)
      ≤ (arrivalLaw n).real {t | Hired theta tau v vhat ihat t istar} := by sorry

end SecretaryPred.LearnedDynkin
