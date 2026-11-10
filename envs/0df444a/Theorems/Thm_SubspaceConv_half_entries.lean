-- Prove2me | Theorems.Thm_SubspaceConv_half_entries
-- name    : SubspaceConv.half_entries
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:31.912128+00:00
-- url     : https://prove2.me/theorems/926a4661-9a25-4c8f-93d2-07c2e633ef89
-- title:
--   §3.3 — at least half the entries go to the cutoff-$(k-1)$ transforms: $M_q(n,k)\ge2M_q(n-1,k)$
-- statement:
--   Let $q=|\mathbb F_q|$. For $n\ge2$ and $1\le k\le n$,
--   $$M_q(n,k)-2M_q(n-1,k)=(q^{n-1}-1)\,M_q(n-2,k-1)-|\mathrm{Gr}_q(n-1,k)|\ \ge 0 .$$
--   For $1\le k<n$,
--   $$|\mathrm{Gr}_q(n-1,k)|=\frac{(q^{n-1}-1)\,|\mathrm{Gr}_q(n-2,k-1)|}{q^k-1};$$
--   for $k=n$ the last count vanishes; and the case $n=1$ is direct. In particular $2M_q(n-1,k)\le M_q(n,k)$ for all $1\le k\le n$.
--
--   This is the inequality that makes the budget induction of §3.3 work: the recursive calls with cutoff $k-1$ hold at least half of the $M_q(n,k)$ entries.
--
--   **Formalization Note** The identity is in $\mathbb Z$ and indexed by $n+2$; the inequality is stated as $2M_q(n,k)\le M_q(n+1,k)$ for $1\le k\le n+1$; the count relation is multiplied out.
--
--   Differences from the source:
--   - reading: the identity, with its range left to the context (k ≥ 1 and k ≤ n, and n ≥ 2 because M_q(n − 2, ·) occurs) → the identity in ℤ for n + 2 ≥ 2 and 1 ≤ k ≤ n + 2; reason: the only range in which every term is defined
--   - encoding: "≥ 0", "n = 1 is direct" → 2 M_q(n, k) ≤ M_q(n + 1, k) for 1 ≤ k ≤ n + 1, which includes the paper's n = 1; reason: the same inequality, shifted by one
--   - encoding: |Gr_q(n − 1, k)| = (q^{n−1} − 1)|Gr_q(n − 2, k − 1)|/(q^k − 1) for 1 ≤ k < n → grCount (n + 1) k · (q^k − 1) = (q^{n+1} − 1) · grCount n (k − 1) for 1 ≤ k < n + 2; reason: division multiplied out; q^k − 1 ≥ 1
--   - encoding: "for k = n the last count vanishes" → |Gr_q(n, n + 1)| = 0 for all n; reason: the same statement with n − 1 written as n
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SubspaceConv_Mq
import Definitions.Def_MinrankTW_gaussCount

namespace SubspaceConv

/-- **The entry inequality of §3.3**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.13 (PDF p.14): at least half the entries
belong to the transforms with cutoff `k − 1`, because
`M_q(n, k) − 2M_q(n − 1, k) = (q^{n−1} − 1)M_q(n − 2, k − 1) − |Gr_q(n − 1, k)| ≥ 0`; for
`1 ≤ k < n`, `|Gr_q(n − 1, k)| = (q^{n−1} − 1)|Gr_q(n − 2, k − 1)|/(q^k − 1)`; for `k = n` the last
count vanishes, and `n = 1` is direct.

**Formalization Note** `q = |F|`. `|Gr_q(n, j)|` is the published definition `MinrankTW.gaussCount F n j` (the number of
`j`-dimensional subspaces of `Fin n → F`, reused from the companion mission). Clause 1 is the identity in `ℤ` for `n + 2 ≥ 2` and
`1 ≤ k ≤ n + 2`. Clause 2 is the inequality `2M_q(n, k) ≤ M_q(n + 1, k)` for `1 ≤ k ≤ n + 1`
(all `n + 1 ≥ 1`, including the paper's `n = 1`). Clause 3 is the count relation multiplied
out (no division), for `1 ≤ k < n + 2`. Clause 4 is "for `k = n` the last count vanishes":
`|Gr_q(n, n + 1)| = 0`. -/
theorem half_entries (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n + 2 →
      (Mq F (n + 2) k : ℤ) - 2 * (Mq F (n + 1) k : ℤ) =
        ((Fintype.card F : ℤ) ^ (n + 1) - 1) * (Mq F n (k - 1) : ℤ) -
          (MinrankTW.gaussCount F (n + 1) k : ℤ)) ∧
    (∀ n k : ℕ, 1 ≤ k → k ≤ n + 1 → 2 * Mq F n k ≤ Mq F (n + 1) k) ∧
    (∀ n k : ℕ, 1 ≤ k → k < n + 2 →
      MinrankTW.gaussCount F (n + 1) k * (Fintype.card F ^ k - 1) =
        (Fintype.card F ^ (n + 1) - 1) * MinrankTW.gaussCount F n (k - 1)) ∧
    (∀ n : ℕ, MinrankTW.gaussCount F n (n + 1) = 0) := by sorry

end SubspaceConv
