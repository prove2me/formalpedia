-- Prove2me | Theorems.Thm_SubspaceConv_budget_induction
-- name    : SubspaceConv.budget_induction
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:15.10583+00:00
-- url     : https://prove2.me/theorems/d68633d8-4609-469c-aa73-0c283e8b3f6c
-- title:
--   §3.3 — the budget induction: cost recurrence $\Rightarrow$ $T(n,k)\le2c\,nkM_q(n,k)$
-- statement:
--   Let $q=|\mathbb F_q|$, $c\ge0$, and let $T(n,k)$ be nonnegative integers with $T(n,0)=0$ for all $n$ ("the case $k=0$ uses no arithmetic") and, for $1\le k\le n$,
--   $$T(n,k)\le T\big(n-1,\min(k,n-1)\big)+T(n-1,k-1)+(q^{n-1}-1)\,T\big(n-2,\min(k-1,n-2)\big)+c\,n\,M_q(n,k).$$
--   Then for all $k\le n$,
--   $$T(n,k)\le 2c\,n\,k\,M_q(n,k).$$
--
--   The hypothesis is the cost recurrence of the recursion: the inside call $Z_{n-1,k}$ with its cutoff clipped to the ambient dimension, the frequency-$0$ call $Z_{n-1,k-1}$, the $q^{n-1}-1$ calls $Z_{n-2,k-1}$ (clipped), and $c\,nM_q(n,k)$ for the local Fourier work. In the paper's words, each entry gets a budget proportional to $nk$; entries of the cutoff-$(k-1)$ calls lose at least $nk-(n-1)(k-1)=n+k-1\ge n$, which, as they are at least half of all entries, leaves at least $nM_q(n,k)/2$ for the Fourier work.
--
--   **Formalization Note** At $n=1$ the factor $q^0-1$ is $0$: only the frequency-$0$ copy occurs. The constant $2c$ is the paper's "leaving at least $nM_q(n,k)/2$".
--
--   Differences from the source:
--   - reading: "give each entry a budget proportional to nk … Induction gives the bound for the transform and its inverse. Clipping each cutoff to its ambient dimension only reduces the budget" → for every T : ℕ → ℕ → ℕ with T(n, 0) = 0 and the displayed recurrence for 1 ≤ k ≤ n, T(n, k) ≤ 2c·nk·M_q(n, k) for k ≤ n; reason: the induction stated for any cost function obeying the recursion's recurrence, with the paper's budget constant; applying it to the programs is the goal's proof
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SubspaceConv_Mq

namespace SubspaceConv

/-- **The budget induction of §3.3**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14): "The case `k = 0` uses no
arithmetic. For `k ≥ 1`, give each entry a budget proportional to `nk`. … leaving at least
`nM_q(n, k)/2` for the local Fourier work. Induction gives the bound … Clipping each cutoff to its
ambient dimension only reduces the budget."

**Formalization Note** The induction is stated for any cost function `T(n, k)` obeying the
recursion's cost recurrence: `T(n, 0) = 0`, and for `1 ≤ k ≤ n`, `T(n, k)` is at most the cost of
`Z_{n−1, min(k, n−1)}` (the inside call, cutoff clipped), of `Z_{n−1, k−1}` (frequency `0`), of
`q^{n−1} − 1` copies of `Z_{n−2, min(k−1, n−2)}` (the nonzero frequencies, eq. (10) with
`d = n − 1`, `ℓ = k − 1`), plus `c n M_q(n, k)` for the local Fourier work. The conclusion is the
bound `T(n, k) ≤ 2c · n k M_q(n, k)`; the constant `2c` is the paper's "leaving at least
`nM_q(n,k)/2`". At `n = 1` the factor `q^0 − 1` is `0`, matching "For `n = 1`, only the copy
labeled by `λ = 0` occurs" (p.6, footnote 4). -/
theorem budget_induction (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (c : ℕ) (T : ℕ → ℕ → ℕ) (hT0 : ∀ n, T n 0 = 0)
    (hT : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      T n k ≤ T (n - 1) (min k (n - 1)) + T (n - 1) (k - 1) +
        (Fintype.card F ^ (n - 1) - 1) * T (n - 2) (min (k - 1) (n - 2)) + c * n * Mq F n k) :
    ∀ n k : ℕ, k ≤ n → T n k ≤ 2 * c * n * k * Mq F n k := by sorry

end SubspaceConv
