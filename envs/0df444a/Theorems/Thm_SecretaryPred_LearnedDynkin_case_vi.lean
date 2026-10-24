-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_case_vi
-- name    : SecretaryPred.LearnedDynkin.case_vi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:57.509311+00:00
-- url     : https://prove2.me/theorems/0eab4304-2962-425a-9f72-112a3469b3f1
-- title:
--   Proof of Theorem 1, case (vi), pp. 9–10 — ı̂ ≠ i∗, ı̂ ∉ M, i∗ ∉ M: E[ALG] ≥ [1/(m+1)·(1−θ)/(1+θ) − τ Σ (m+1 k)(−1)^k(1−τ^k)/k − (1−τ)/(m+1)·{1−(1−τ)^(m+1)}]·v(i∗)
-- statement:
--   Let $n$ candidates have values $v(i)\ge 0$ and predictions $\hat v(i)\ge 0$, let $\hat\imath$ be any maximizer of $\hat v$, and let $i^*$ be the best candidate (largest value, ties broken by the smaller index). Run Algorithm 1 (learned Dynkin) with threshold $\theta\ge 0$ and time $\tau\in(0,1)$ on independent Uniform$[0,1]$ arrival times. $M$ is the set of candidates with $|1-\hat v(i)/v(i)|>\theta$ and $m=|M|$.
--
--   **Case (vi).** Suppose $M\neq\emptyset$, $\hat\imath\neq i^*$, $\hat\imath\notin M$ and $i^*\notin M$. Then the expected value of the algorithm satisfies
--
--   $$\mathbb E[\mathrm{ALG}]\;\ge\;\Bigl[\frac{1}{m+1}\cdot\frac{1-\theta}{1+\theta}-\tau\sum_{k=1}^{m+1}\binom{m+1}{k}(-1)^{k}\frac{1-\tau^k}{k}-\frac{1-\tau}{m+1}\bigl\{1-(1-\tau)^{m+1}\bigr\}\Bigr]\,v(i^*).$$
--
--   The first term is the contribution of hiring $\hat\imath$ (probability $1/(m+1)$, value at least $(1-\theta)/(1+\theta)\,v(i^*)$ by inequality (2)); the rest is the probability of hiring $i^*$. Unlike cases (i)–(v), this bounds the expected value, not a probability.
--
--   **Formalization Note** Candidates are `Fin n` (0-based). $\mathbb E[\mathrm{ALG}]$ is `expectedValue θ τ v v̂ ı̂`, the integral of the value of the run against the uniform law on $[0,1]^n$. $i^*$ is the top candidate of the tie-broken order `Beats`, and $\hat\imath$ is any maximizer of $\hat v$.
--
--   Differences from the source:
--   - generalization: θ = 0.646, τ = 0.313 (Theorem 1) → any θ ≥ 0 and τ with 0 < τ < 1; reason: the case derivations never use the values of θ and τ (the paper evaluates the six case bounds on a grid of (θ, τ), p. 10); at θ = 0.646, τ = 0.313 the item is the source's step
--   - encoding: 'the competitive ratio can be bounded from below by X' → X·v(i∗) ≤ E[ALG]; reason: the competitive ratio is E[ALG]/v(i∗) with v(i∗) = max_i v(i); the product form also covers v(i∗) = 0
--   - reading: line 8 of Algorithm 1: 'i is the best so far', with ties not addressed; i∗ ∈ argmax v → i beats every earlier arrival in the strict order 'larger value, then smaller index' (Beats); istar is the top candidate of that order; reason: both untied readings make Theorem 1 false: strictly larger value fails for n ≥ 5 candidates all with v = 1 and exact predictions except v̂(ı̂) = 10 (P(hire) ≤ 1/n < 0.215); weakly larger value fails for i∗ with v = v̂ = 1, ı̂ with v = δ, v̂ = 10 and n − 2 fillers with v = v̂ = δ (ratio → δ as n → ∞); for distinct values the order is the source's
--   - encoding: |1 − v̂(i)/v(i)| > θ (line 4 and the set M, p. 6) → θ·v(i) < |v(i) − v̂(i)| (Deviates); reason: identical when v(i) > 0; avoids Lean's x/0 = 0, and for v(i) = 0 a candidate deviates iff v̂(i) ≠ 0
--   - encoding: candidates N = [n] interviewed in random order, arrival times iid Uniform[0, 1] (§2.1), exactly one hire → candidates Fin n (0-based), t uniform on the cube [0, 1]^n (arrivalLaw n), the mode at i is Secretary iff some deviating j has t_j ≤ t_i, and algValue sums the values of all candidates that are first to stop; reason: the run differs from the source's single-hire run only on the null set of arrival vectors with two equal times
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, pp. 9–10, proof of Theorem 1, case (vi)

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem case_vi (n : ℕ) (theta tau : ℝ) (v vhat : Fin n → ℝ) (ihat istar : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hvhat : ∀ i, 0 ≤ vhat i) (hihat : ∀ j, vhat j ≤ vhat ihat)
    (histar : ∀ j, j ≠ istar → Beats v istar j)
    (htheta : 0 ≤ theta) (htau0 : 0 < tau) (htau1 : tau < 1)
    (hcase : ihat ≠ istar) (hhatM : ¬ Deviates theta v vhat ihat)
    (hstarM : ¬ Deviates theta v vhat istar)
    (hMne : (Mset theta v vhat).Nonempty) (m : ℕ) (hm : (Mset theta v vhat).card = m) :
    (1 / ((m : ℝ) + 1) * ((1 - theta) / (1 + theta))
        - tau * ∑ k ∈ Finset.Icc 1 (m + 1),
            ((m + 1).choose k : ℝ) * (-1 : ℝ) ^ k * (1 - tau ^ k) / (k : ℝ)
        - (1 - tau) / ((m : ℝ) + 1) * (1 - (1 - tau) ^ (m + 1))) * v istar
      ≤ expectedValue theta tau v vhat ihat := by sorry

end SecretaryPred.LearnedDynkin
