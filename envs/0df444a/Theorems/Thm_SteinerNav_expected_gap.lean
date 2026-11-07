-- Prove2me | Theorems.Thm_SteinerNav_expected_gap
-- name    : SteinerNav.expected_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:16.862266+00:00
-- url     : https://prove2.me/theorems/9b97174e-e32f-402d-9db0-3ebe9a5e7ce4
-- title:
--   Proof of Theorem 3, p.9 — $\mathbb E Z_t=(n-m)/(m+1)$ for a uniform sample of $m$ positions
-- statement:
--   Let $1\le m\le n$. Choose a set $Q$ of $m$ positions uniformly at random among the positions $0,1,\dots,n-1$, and let $Z$ be the number of positions before the first chosen one. Then
--   $$\mathbb E Z=\frac{n-m}{m+1}.$$
--
--   In the proof of Theorem 3 the positions are the input points sorted by distance from a target $t$, the chosen positions are the landmarks, and $Z=Z_t$ counts the entries before the first landmark; every type-3 edge entering $t$ has its source among them.
--
--   **Formalization Note** The expectation is the exact average over all $\binom nm$ subsets of size $m$ of $\{0,\dots,n-1\}$, computed in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: "for each target t sort all n input points by distance from t … for a uniform sample of m positions" → positions 0, …, n−1 directly, with the uniform sample an average over m-subsets; reason: Z_t depends on the sample only through the positions of the landmarks in the sorted order.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9 (display EZ_t = (n − m)/(m + 1))

import Mathlib

namespace SteinerNav

/-- Proof of Theorem 3, `E Z_t`: for `m` uniform positions among `n` (`1 ≤ m ≤ n`), the expected number
of positions before the first sampled one is `(n − m)/(m + 1)`, written as an exact average over the
`m`-subsets of `{0, …, n − 1}` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse
α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256
e396eee6…), proof of Theorem 3, p.9). -/
theorem expected_gap (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ Q ∈ (Finset.range n).powersetCard m,
        (((Finset.range n).filter fun i => ∀ q ∈ Q, i < q).card : ℝ)) / (n.choose m : ℝ) =
      ((n : ℝ) - m) / ((m : ℝ) + 1) := by sorry

end SteinerNav
