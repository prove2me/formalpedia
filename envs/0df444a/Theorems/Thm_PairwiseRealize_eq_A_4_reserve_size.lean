-- Prove2me | Theorems.Thm_PairwiseRealize_eq_A_4_reserve_size
-- name    : PairwiseRealize.eq_A_4_reserve_size
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:42.123637+00:00
-- url     : https://prove2.me/theorems/fd8a2196-1ddf-4f6d-80ca-79293bf2a643
-- title:
--   (A.4), p.12 — the reserve size $L=O(n^2\log(n+1))$, the forest counts and sums (corrected: fewer than $2D_2$ nodes for $n\ge2$, $L\ge4C_0m\ell$ for $n\ge3$)
-- statement:
--   For the trees and budgets of §A.2, with $D_2=\binom n2$:
--
--   1. there is a constant $K$ with $L\le Kn^2\log(n+1)$ for every $n\ge1$;
--   2. for $n\ge2$ the forest has fewer than $2D_2$ nodes;
--   3. for $n\ge1$ the forest has $D_2$ leaves, $\sum_Rd_R\le D_2(1+2\lceil\log_2n\rceil)$ and $\sum_{R\text{ root}}\lceil\sqrt{d_R}\rceil\le(n/2)\lceil\log_2n\rceil+n-1$;
--   4. for $n\ge3$, $L\ge4C_0m\ell$.
--
--   Items 1 and 4 are what the matrix concentration needs: the reserve is small enough to be hidden in the depth, and large enough for the spectral tail bound to vanish.
--
--   Differences from the source:
--   - correction: The top padding ensures L ≥ 4C₀mℓ (n unrestricted) → L ≥ 4C₀mℓ for n ≥ 3; reason: false at n = 2: the only split of {1,2} gives the root {1}×{2}, a leaf with no padding, so L = 70t = 5.6·10⁶ (m = 4, t = 80000) while 4C₀mℓ = 4·2⁴⁴·4·2 ≈ 5.6·10¹⁴
--   - correction: The forest has fewer than 2D₂ nodes (n unrestricted) → for n ≥ 2; reason: false at n = 1: the forest is empty and D₂ = 0, so "fewer than 2·0 nodes" fails
--   - encoding: balanced halves; the longer side; O(n² log(n+1)); n a dimension of the cube → first ⌊s/2⌋ and last ⌈s/2⌉ elements; A on ties; ∃ K, ∀ n ≥ 1; the leaf count and the two sums for every n ≥ 1; reason: the paper leaves the tie-breaks open and the claims hold for every balanced choice; at n = 0 the right side n − 1 of the root sum is negative and log(n + 1) = 0, so n ≥ 1 is the domain of the claims
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, (A.4), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PairwiseRealize_Reserve

namespace PairwiseRealize

/-- **The reserve size (A.4), §A.2 p.12 (PDF p.13), corrected: the padding claim for `n ≥ 3`.**
K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…): "The reserve size is L = 6t + 8nt + 4 Σ_{R internal} k_R +
8 Σ_{R leaf} T_R = O(n² log(n + 1)). (A.4) For completeness, write D2 = (n choose 2). The forest has
D2 leaves and fewer than 2D2 nodes, and Σ_R d_R ≤ D2(1 + 2⌈log₂ n⌉),
Σ_{R root} ⌈√d_R⌉ ≤ (n/2)⌈log₂ n⌉ + n − 1. […] These bounds prove (A.4). The top padding ensures
L ≥ 4C0mℓ."

For the trees and budgets of §A.2 (`forest`, `reserveSize`):
1. `L = O(n² log(n + 1))`: there is `K` with `L ≤ K n² log(n + 1)` for every `n ≥ 1`;
2. for `n ≥ 2` the forest has fewer than `2 (n choose 2)` nodes;
3. for `n ≥ 1` the forest has `(n choose 2)` leaves, `Σ_R d_R ≤ (n choose 2)(1 + 2⌈log₂ n⌉)` and
   `Σ_{R root} ⌈√d_R⌉ ≤ (n/2)⌈log₂ n⌉ + n − 1`;
4. for `n ≥ 3`, `L ≥ 4 C0 m ℓ`.

**Formalization Note** Item 4 is false at `n = 2` as printed: the only split of `{1, 2}` gives the
root `{1} × {2}`, a leaf, which gets no padding, so `L = 6t + 16t + 48t = 70t = 5.6·10⁶` while
`4C0mℓ = 4·2⁴⁴·4·2 ≈ 5.6·10¹⁴`. It is stated for `n ≥ 3`. The node count of item 2 is false at `n = 1`
(the forest is empty and "fewer than `2·0`" fails), so it is stated for `n ≥ 2`; the leaf count and the
two sums hold for every `n ≥ 1` and are stated so. `ln` is the
natural logarithm (the base only changes `K`). -/
theorem eq_A_4_reserve_size :
    (∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → (reserveSize n : ℝ) ≤ K * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → (forest n).length < 2 * n.choose 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      ((forest n).filter fun R => R.leaf).length = n.choose 2 ∧
      ((forest n).map Node.d).sum ≤ n.choose 2 * (1 + 2 * Nat.clog 2 n) ∧
      ((((forest n).filter fun R => R.root).map fun R => ceilSqrt R.d).sum : ℝ) ≤
        (n : ℝ) / 2 * (Nat.clog 2 n : ℝ) + n - 1) ∧
    ∀ n : ℕ, 3 ≤ n → 4 * C0 * mDim n * ell n ≤ reserveSize n := by sorry

end PairwiseRealize
