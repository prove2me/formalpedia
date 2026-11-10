-- Prove2me | Theorems.Thm_SubspaceConv_eq_11
-- name    : SubspaceConv.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:07.210196+00:00
-- url     : https://prove2.me/theorems/8890c61e-a976-4dd9-b023-963460cb22b6
-- title:
--   Eq. (11) — the Goldman–Rota recurrence with a cutoff for $M_q(n,k)$
-- statement:
--   Let $q=|\mathbb F_q|$. The number $M_q(n,k)$ of subspaces of $\mathbb F_q^n$ of dimension at most $k$ satisfies
--   $$M_q(n,k)=\sum_{j=0}^{\min(k,n)}|\mathrm{Gr}_q(n,j)|$$
--   and, for $n\ge2$,
--   $$M_q(n,k)=M_q(n-1,k)+M_q(n-1,k-1)+(q^{n-1}-1)\,M_q(n-2,k-1),\tag{11}$$
--   with the convention that a negative cutoff gives an empty table, so that at $k=0$ the identity reads $M_q(n,0)=M_q(n-1,0)$.
--
--   The three terms are the table lengths of the recursive calls: the inside call $Z_{n-1,k}$, the frequency $\lambda=0$ call $Z_{n-1,k-1}$, and the $q^{n-1}-1$ calls $Z_{n-2,k-1}$ at the nonzero frequencies. So the recursion does not increase the number of entries.
--
--   **Formalization Note** The recurrence is stated for $n+2$ and cutoff $k+1$, with the cutoff-$0$ case as a separate clause.
--
--   Differences from the source:
--   - encoding: (11) for n ≥ 2 and integer cutoffs, with empty tables for negative cutoffs → the identity for n + 2 and cutoff k + 1, plus M_q(n + 2, 0) = M_q(n + 1, 0); reason: natural-number arithmetic; every instance of the printed identity is covered
--   - encoding: M_q(n, k) defined as ∑_{j≤min(k,n)} |Gr_q(n, j)| → M_q(n, k) defined as the number of subspaces of dimension at most k, with the sum as a clause; reason: the same number
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, eq. (11), p.12 (PDF p.13); §1.1, p.1 (definition of M_q)

import Mathlib
import Definitions.Def_SubspaceConv_Mq
import Definitions.Def_MinrankTW_gaussCount

namespace SubspaceConv

/-- **Eq. (11)** (Goldman–Rota recurrence with a cutoff), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.3, p.12 (PDF p.13):
`M_q(n, k) = M_q(n − 1, k) + M_q(n − 1, k − 1) + (q^{n−1} − 1) M_q(n − 2, k − 1)` for `n ≥ 2`,
together with the definition `M_q(n, k) = ∑_{j=0}^{min(k,n)} |Gr_q(n, j)|` (§1.1, p.1).

**Formalization Note** `q = |F|`. `|Gr_q(n, j)|` is the published definition `MinrankTW.gaussCount F n j` (the number of
`j`-dimensional subspaces of `Fin n → F`, reused from the companion mission). The recurrence is stated with `n + 2` for the paper's
`n ≥ 2`, and with cutoff `k + 1`; the cutoff `0` is the separate clause
`M_q(n + 2, 0) = M_q(n + 1, 0)`, which is (11) at `k = 0` with the paper's convention of empty
tables for negative cutoffs (§2, p.10). -/
theorem eq_11 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (∀ n k : ℕ, Mq F n k = ∑ j ∈ Finset.range (min k n + 1), MinrankTW.gaussCount F n j) ∧
    (∀ n k : ℕ, Mq F (n + 2) (k + 1) =
      Mq F (n + 1) (k + 1) + Mq F (n + 1) k + (Fintype.card F ^ (n + 1) - 1) * Mq F n k) ∧
    (∀ n : ℕ, Mq F (n + 2) 0 = Mq F (n + 1) 0) := by sorry

end SubspaceConv
