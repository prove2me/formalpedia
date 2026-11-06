-- Prove2me | Theorems.Thm_PLIAG_lemma_4_2
-- name    : PLIAG.lemma_4_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:26:46.672143+00:00
-- url     : https://prove2.me/theorems/44c7efdb-bf83-4599-a877-061605843523
-- title:
--   Lemma 4.2 — geometric decay of a delayed nonnegative recursion ([1, Lemma 1])
-- statement:
--   Let $\{V_k\}_{k\ge0}$ and $\{w_k\}_{k\ge0}$ be nonnegative sequences of real numbers satisfying
--
--   $$
--   V_{k+1}\ \le\ aV_k-bw_k+c\sum_{j=k-k_0}^{k}w_j\qquad\text{for all }k\ge0,
--   $$
--
--   where $a\in(0,1)$, $b\ge0$, $c\ge0$, $k_0\ge0$, and $w_k=0$ for $k<0$. Assume moreover
--
--   $$
--   \frac{c}{1-a}\cdot\frac{1-a^{k_0+1}}{a^{k_0}}\ \le\ b. \tag{4.4}
--   $$
--
--   Then $V_k\le a^kV_0$ for all $k\ge0$.
--
--   The lemma, due to Aytekin, Feyzmahdavian and Johansson, turns a one-step contraction perturbed by the last $k_0+1$ increments into a clean geometric rate, provided the penalty $b$ dominates the accumulated perturbation.
--
--   Differences from the source:
--   - encoding: w_k = 0 for k < 0 and Σ_{j=k−k_0}^k → sequences indexed by ℕ, Σ over Finset.Icc (k − k_0) k with truncated subtraction; reason: for k < k_0 the range is {0, …, k}, exactly the paper’s nonzero terms; each index counted once
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Lemma 4.2, p.12

import Mathlib

namespace PLIAG

/-- **Lemma 4.2** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, p.12; Aytekin–Feyzmahdavian–Johansson
[1, Lemma 1]). Let `{V_k}`, `{w_k}` be nonnegative sequences with
`V_{k+1} ≤ a V_k − b w_k + c Σ_{j=k−k_0}^k w_j` for all `k ≥ 0`, where `a ∈ (0, 1)`, `b ≥ 0`,
`c ≥ 0`, `k_0 ≥ 0`, `w_k = 0` for `k < 0`, and `(c/(1−a)) · (1 − a^{k_0+1})/a^{k_0} ≤ b` (4.4).
Then `V_k ≤ a^k V_0` for all `k ≥ 0`.

**Formalization Note.** Real sequences indexed by `ℕ`. The convention `w_k = 0` for `k < 0` is
encoded by summing over `Finset.Icc (k − k_0) k` with truncated subtraction: for `k < k_0` this
is `{0, …, k}`, exactly the paper's nonzero terms. -/
theorem lemma_4_2 (V wseq : ℕ → ℝ) (a b c : ℝ) (k₀ : ℕ)
    (hV : ∀ k, 0 ≤ V k) (hw : ∀ k, 0 ≤ wseq k)
    (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hrec : ∀ k, V (k + 1) ≤ a * V k - b * wseq k + c * ∑ j ∈ Finset.Icc (k - k₀) k, wseq j)
    (hcond : c / (1 - a) * ((1 - a ^ (k₀ + 1)) / a ^ k₀) ≤ b) :
    ∀ k, V k ≤ a ^ k * V 0 := by sorry

end PLIAG
