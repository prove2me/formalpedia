-- Prove2me | Theorems.Thm_VehShare_MultiNet_chu_vandermonde_real
-- name    : VehShare.MultiNet.chu_vandermonde_real
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T04:06:10.103469+00:00
-- url     : https://prove2.me/theorems/1b868fd6-cfcb-4213-8264-0ed144c74ece
-- title:
--   Chu–Vandermonde identity with real parameters
-- statement:
--   For all real numbers $T,T_1$ and every integer $K\ge0$,
--
--   $$
--   \sum_{K_1=0}^{K}\binom{K+T-K_1-T_1-1}{K-K_1}\binom{T_1+K_1-1}{K_1}=\binom{K+T-1}{K},
--   $$
--
--   where $\binom{x}{k}=\prod_{i=0}^{k-1}(x-i)/k!$ is the generalized binomial coefficient.
--
--   In the proof of Theorem 4 (with $T_i=N_i+M_i$, $T=T_1+T_2$) the identity makes the products $\binom{K+T-K_1-T_1-1}{K-K_1}\binom{T_1+K_1-1}{K_1}/\binom{K+T-1}{K}$ a probability distribution over the splits $K=K_1+K_2$, which is averaged against in the case of two networks.
--
--   Differences from the source:
--   - generalization: T_i = N_i + M_i and T = T_1 + T_2 → arbitrary real T and T₁; reason: the identity holds for all real parameters; the paper's values are a special case
--   - encoding: the binomial coefficient defined by Π_{i=0}^{K−1}(K+T−1−i)/K! if K ≥ 0 and 0 if K < 0 → Ring.choose x k for k ∈ ℕ; reason: the same product formula; the lower indices K − K1, K1, K are natural numbers here, so the case K < 0 never arises
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, proof of Theorem 4, p. 18

import Mathlib

namespace VehShare.MultiNet

/-- **Chu–Vandermonde identity with real parameters.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), proof of Theorem 4, p. 18 (unnumbered display).

For all real `T, T₁` and every `K ∈ ℕ`:
`∑_{K₁=0}^{K} C(K+T−K₁−T₁−1, K−K₁) · C(T₁+K₁−1, K₁) = C(K+T−1, K)`,
where `C(x, k) = ∏_{i=0}^{k−1}(x − i)/k!` is the generalized binomial coefficient.

**Formalization Note.** `Ring.choose x k` is that coefficient. The paper has `T_i = N_i + M_i`; the
identity is stated for all real `T, T₁` (a generalization). -/
theorem chu_vandermonde_real (T T₁ : ℝ) (K : ℕ) :
    ∑ K₁ ∈ Finset.range (K + 1),
        Ring.choose ((K : ℝ) + T - K₁ - T₁ - 1) (K - K₁) * Ring.choose (T₁ + K₁ - 1) K₁ =
      Ring.choose ((K : ℝ) + T - 1) K := by sorry

end VehShare.MultiNet
