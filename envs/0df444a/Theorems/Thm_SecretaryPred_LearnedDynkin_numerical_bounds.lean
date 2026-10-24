-- Prove2me | Theorems.Thm_SecretaryPred_LearnedDynkin_numerical_bounds
-- name    : SecretaryPred.LearnedDynkin.numerical_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:46.093623+00:00
-- url     : https://prove2.me/theorems/b8464ebe-0fc1-4345-bfd1-19a5a9c246e9
-- title:
--   Proof of Theorem 1, numerical bounds, pp. 7 and 10 — at θ = 0.646, τ = 0.313: (1−θ)/(1+θ) ≥ 0.215, τ ln(1/τ) ≥ 0.363, and the bounds of cases (ii), (iv), (v), (vi) are ≥ 0.215 for every m ≥ 1
-- statement:
--   Fix the parameters of Theorem 1, $\theta=0.646$ and $\tau=0.313$. Then:
--   1. $\dfrac{1-\theta}{1+\theta}\ge 0.215$;
--   2. $\tau\ln\dfrac1\tau\ge 0.363$ (the bound of cases (i) and (iii));
--   3. for every integer $m\ge 1$, each of the following case bounds is at least $0.215$:
--
--   $$\text{(ii)}\quad \frac{1}{m+1}+\tau\sum_{k=1}^{m}\binom{m}{k}(-1)^{k-1}\frac{1-\tau^k}{k},\qquad \text{(iv)}\quad \tau\sum_{k=1}^{m}\binom{m}{k}(-1)^{k-1}\frac{1-\tau^k}{k},$$
--
--   $$\text{(v)}\quad \frac{(1-\tau)^{m+1}}{m+1}-\tau\sum_{k=1}^{m}\binom{m}{k}(-1)^{k}\frac{1-\tau^k}{k}-\frac{1-\tau}{m}\bigl\{1-(1-\tau)^m\bigr\},$$
--
--   $$\text{(vi)}\quad \frac{1}{m+1}\cdot\frac{1-\theta}{1+\theta}-\tau\sum_{k=1}^{m+1}\binom{m+1}{k}(-1)^{k}\frac{1-\tau^k}{k}-\frac{1-\tau}{m+1}\bigl\{1-(1-\tau)^{m+1}\bigr\}.$$
--
--   These are the numerical facts that turn the six case bounds into the constant $0.215$ of Theorem 1. The margins are thin: the case (iv) bound at $m=1$ is $\tau(1-\tau)=0.215031$ and the case (vi) bound at $m=1$ is about $0.215049$.
--
--   **Formalization Note** The decimals are exact rationals in Lean ($0.646 = 646/1000$, $0.313 = 313/1000$); $\ln$ is `Real.log`.
--
--   Differences from the source:
--   - reading: 'the competitive ratio is at least 0.215 for all m' in cases (iv), (v), (vi), and 'the competitive ratio for the case (ii) is at least its second term' → the closed-form bound of each of cases (ii), (iv), (v), (vi) is ≥ 0.215 for every m ≥ 1; reason: the paper's case competitive ratios are these closed-form lower bounds; the (ii) clause is stated directly instead of through the comparison with (iv)
-- source:
--   Fujii, Yoshida, The Secretary Problem with Predictions, arXiv:2306.08340v1, p. 7 (case M = ∅: (1−0.646)/(1+0.646) ≥ 0.215) and p. 10 (the paragraph after case (vi))

import Mathlib
import Definitions.Def_SecretaryPred_LearnedDynkin_Setting

namespace SecretaryPred.LearnedDynkin

theorem numerical_bounds :
    (0.215 : ℝ) ≤ (1 - 0.646) / (1 + 0.646) ∧
      (0.363 : ℝ) ≤ 0.313 * Real.log (1 / 0.313) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ 1 / ((m : ℝ) + 1) + 0.313 * ∑ k ∈ Finset.Icc 1 m,
          (m.choose k : ℝ) * (-1 : ℝ) ^ (k - 1) * (1 - 0.313 ^ k) / (k : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ 0.313 * ∑ k ∈ Finset.Icc 1 m,
          (m.choose k : ℝ) * (-1 : ℝ) ^ (k - 1) * (1 - 0.313 ^ k) / (k : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ (1 - 0.313) ^ (m + 1) / ((m : ℝ) + 1)
          - 0.313 * ∑ k ∈ Finset.Icc 1 m,
              (m.choose k : ℝ) * (-1 : ℝ) ^ k * (1 - 0.313 ^ k) / (k : ℝ)
          - (1 - 0.313) / (m : ℝ) * (1 - (1 - 0.313) ^ m)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (0.215 : ℝ) ≤ 1 / ((m : ℝ) + 1) * ((1 - 0.646) / (1 + 0.646))
          - 0.313 * ∑ k ∈ Finset.Icc 1 (m + 1),
              ((m + 1).choose k : ℝ) * (-1 : ℝ) ^ k * (1 - 0.313 ^ k) / (k : ℝ)
          - (1 - 0.313) / ((m : ℝ) + 1) * (1 - (1 - 0.313) ^ (m + 1))) := by sorry

end SecretaryPred.LearnedDynkin
