-- Prove2me | Theorems.Thm_RandMatDisc_lemma_3_9
-- name    : RandMatDisc.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:40:00.174852+00:00
-- url     : https://prove2.me/theorems/90adad4d-7535-44f5-9465-9eac762801aa
-- title:
--   Lemma 3.9 — scalar contraction
-- statement:
--   For every $C>0$ there is $A\in[1,\infty)$ with the following property. If $(y_k)_{k\ge0}$ is a non-negative sequence with
--
--   $$y_{k+1}\le C(\sqrt{y_k}+1)\qquad\text{for all }k,$$
--
--   then $y_k\le A$ for all $k\ge\lceil\log_2(\max\{y_0,1\})\rceil$, and $y_k\le\max\{y_0,A\}$ for all $k$.
--
--   Applied to $y_k=tR_k/D$, it shows that $K_d$ rounds bring the residual of the algorithm down to order $D/t$.
--
--   Differences from the source: none.
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), Lemma 3.9, p.21 (PDF p.23), eq. (37)

import Mathlib

namespace RandMatDisc

/-- **Lemma 3.9 (Scalar contraction)**, Kızıldağ, Li, arXiv:2610.01591 (held file sha256
889af7fc…), p.21 (PDF p.23).

For every `C > 0` there is `A ∈ [1, ∞)` such that every non-negative sequence `(y_k)_{k ≥ 0}`
with `y_{k+1} ≤ C(√y_k + 1)` (37) satisfies `y_k ≤ A` for all `k ≥ ⌈log₂(max{y₀, 1})⌉`, and
`y_k ≤ max{y₀, A}` for all `k`.

**Formalization Note.** `⌈log₂ ·⌉` is `Nat.ceil (Real.logb 2 ·)`; its argument is at least `1`,
so the logarithm is non-negative. -/
theorem lemma_3_9 :
    ∀ C : ℝ, 0 < C → ∃ A : ℝ, 1 ≤ A ∧ ∀ y : ℕ → ℝ, (∀ k, 0 ≤ y k) →
      (∀ k, y (k + 1) ≤ C * (Real.sqrt (y k) + 1)) →
      (∀ k : ℕ, ⌈Real.logb 2 (max (y 0) 1)⌉₊ ≤ k → y k ≤ A) ∧
      (∀ k, y k ≤ max (y 0) A) := by sorry

end RandMatDisc
