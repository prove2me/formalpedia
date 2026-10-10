-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_product_bounds
-- name    : StochGradTrack.Dimin.product_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:51.713168+00:00
-- url     : https://prove2.me/theorems/9a6bcbcf-9f01-4e2e-8d86-6e86f6267483
-- title:
--   Lemma 4.1 of [44], p. 427 — ∏(1 − θμ/(m+t)) ≤ m^{θμ}/(m+k)^{θμ} and ∏_{j=t+1}^{k−1}(1 − θμ/(m+j)) ≤ (m+t+1)^{θμ}/(m+k)^{θμ}
-- statement:
--   Let $m>0$ and $0\le\theta\mu\le m$. For every $k\ge0$,
--   $$\prod_{t=0}^{k-1}\Big(1-\frac{\theta\mu}{m+t}\Big)\le\frac{m^{\theta\mu}}{(m+k)^{\theta\mu}},$$
--   and for every $0\le t<k$,
--   $$\prod_{j=t+1}^{k-1}\Big(1-\frac{\theta\mu}{m+j}\Big)\le\frac{(m+t+1)^{\theta\mu}}{(m+k)^{\theta\mu}},$$
--   an empty product being $1$.
--
--   These bounds control the products that appear when the recursion $U_{k+1}\le(1-\alpha_k\mu)U_k+\cdots$ is unrolled.
--
--   **Formalization Note** The page quotes the bounds from Lemma 4.1 of reference [44] without hypotheses on $\theta\mu$; $\theta\mu\le m$ holds in Theorem 2 (from $m>\frac\theta2(\mu+L)$ and $\mu\le L$) and keeps every factor nonnegative, without which the bounds fail. Powers with exponent $\theta\mu$ are real powers.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.3, p. 427 (product bounds, citing Lemma 4.1 of [44])

import Mathlib

namespace StochGradTrack.Dimin

/-- The product bounds quoted from Lemma 4.1 of [44] (p. 427), for `0 ≤ θμ ≤ m` and `m > 0`. -/
theorem product_bounds (θ μ m : ℝ) (h0 : 0 ≤ θ * μ) (hle : θ * μ ≤ m) (hm : 0 < m) (k : ℕ) :
    ∏ t ∈ Finset.range k, (1 - θ * μ / (m + t)) ≤ m ^ (θ * μ) / (m + k) ^ (θ * μ) ∧
    ∀ t : ℕ, t < k →
      ∏ j ∈ Finset.Ico (t + 1) k, (1 - θ * μ / (m + j)) ≤ (m + t + 1) ^ (θ * μ) / (m + k) ^ (θ * μ) := by sorry

end StochGradTrack.Dimin
