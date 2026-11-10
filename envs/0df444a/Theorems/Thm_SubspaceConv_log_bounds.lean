-- Prove2me | Theorems.Thm_SubspaceConv_log_bounds
-- name    : SubspaceConv.log_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:05.74911+00:00
-- url     : https://prove2.me/theorems/5611cb3e-5390-45ec-b144-3d6e2be8405c
-- title:
--   §3.3 — $\log_qM_q(n,k)\ge k(n-k)\ge nk/2$ for $k\le n/2$, $\ge\lfloor n^2/4\rfloor=\Omega(nk)$ for $k>n/2$
-- statement:
--   Let $q=|\mathbb F_q|$.
--
--   1. For $1\le k\le n/2$: $\log_qM_q(n,k)\ge k(n-k)\ge nk/2$.
--   2. For $k>n/2$: $\log_qM_q(n,k)\ge\lfloor n^2/4\rfloor$.
--   3. $\lfloor n^2/4\rfloor=\Omega(nk)$ for $k\le n$: explicitly $nk\le4\lfloor n^2/4\rfloor+1$.
--
--   Together these give $nk=O(\log M_q(n,k))$ whenever $n,k\ge1$, which turns the bound $O_q(nkM_q(n,k))$ of Theorem 1 into $O_q(M_q(n,k)\log M_q(n,k))$.
--
--   **Formalization Note** $\log_q$ is `Real.logb q`, and $\lfloor n^2/4\rfloor$ is natural-number division. Item 2 is stated for every $k$ with $n<2k$, including $k>n$ (cutoffs above $n$ are clipped). The $+1$ in item 3 is needed at $n=k=1$.
--
--   Differences from the source:
--   - encoding: log_q, ⌊n²/4⌋ → Real.logb q, n^2/4 in ℕ; reason: same values
--   - encoding: "⌊n²/4⌋ = Ω(nk)" → n·k ≤ 4·⌊n²/4⌋ + 1 for k ≤ n; reason: an explicit constant for Ω
--   - generalization: "for k > n/2" (with k ≤ n from Theorem 1) → for every k with n < 2k; reason: for k > n the count M_q(n, k) equals M_q(n, n); the k ≤ n instances are the paper's
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SubspaceConv_Mq

namespace SubspaceConv

/-- **The logarithmic bounds of §3.3**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14): "For `1 ≤ k ≤ n/2`, (24)
gives `log_q M_q(n, k) ≥ k(n − k) ≥ nk/2`. For `k > n/2`, the middle-dimensional term gives
`log_q M_q(n, k) ≥ ⌊n²/4⌋ = Ω(nk)`."

**Formalization Note** `q = |F|` and `log_q` is `Real.logb q`. Clause 1: for `1 ≤ k`, `2k ≤ n`,
`k(n − k) ≤ log_q M_q(n, k)` and `nk ≤ 2k(n − k)`. Clause 2: for `n < 2k` (no upper bound on `k`
is needed, since cutoffs above `n` are clipped), `⌊n²/4⌋ ≤ log_q M_q(n, k)`; `⌊n²/4⌋` is the
natural-number division `n^2 / 4`. Clause 3 is "`⌊n²/4⌋ = Ω(nk)`" with explicit constants:
`nk ≤ 4⌊n²/4⌋ + 1` for `k ≤ n` (the `+1` is needed at `n = k = 1`, where `⌊n²/4⌋ = 0`). -/
theorem log_bounds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (∀ n k : ℕ, 1 ≤ k → 2 * k ≤ n →
      ((k * (n - k) : ℕ) : ℝ) ≤ Real.logb (Fintype.card F) (Mq F n k) ∧
        n * k ≤ 2 * (k * (n - k))) ∧
    (∀ n k : ℕ, n < 2 * k → ((n ^ 2 / 4 : ℕ) : ℝ) ≤ Real.logb (Fintype.card F) (Mq F n k)) ∧
    (∀ n k : ℕ, k ≤ n → n * k ≤ 4 * (n ^ 2 / 4) + 1) := by sorry

end SubspaceConv
