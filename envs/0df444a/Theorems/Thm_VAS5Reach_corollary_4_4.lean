-- Prove2me | Theorems.Thm_VAS5Reach_corollary_4_4
-- name    : VAS5Reach.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:25:39.570719+00:00
-- url     : https://prove2.me/theorems/4929811c-2f55-487b-8425-634cf23044e1
-- title:
--   Corollary 4.4 — Steinitz reordering with nonzero sum: $p_k \ge \min(0,z) - dM\mathbf 1$ (corrected: $M \ge 0$)
-- statement:
--   Let $v_1, \dots, v_n \in \mathbb Q^d$ have max norm at most $M$, where $M \ge 0$, and let $z := \sum_{i=1}^n v_i$. There is a permutation $\sigma$ of $[n]$ such that every partial sum $p_k = \sum_{i=1}^k v_{\sigma(i)}$, $0 \le k \le n$, satisfies
--   $$
--   p_k \ge \min(0, z) - dM \cdot \mathbf 1 ,
--   $$
--   the minimum taken componentwise. It is used to reorder the relocated cycles in the proof of Theorem 4.2.
--
--   Differences from the source:
--   - correction: v₁, …, vₙ of norm at most M (M unrestricted) → additionally 0 ≤ M; reason: as printed the statement fails for n = 0, d = 1, M = −1: the empty partial sum 0 would have to be ≥ 0 − 1·(−1) = 1; a bound on norms is nonnegative, and for n ≥ 1 the hypothesis already forces M ≥ 0
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 4.4, p.18 (PDF p.20)

import Mathlib

namespace VAS5Reach

/-- **Corollary 4.4.** Let `v₁, …, vₙ ∈ ℚ^d` have norm at most `M`, and let `z := Σᵢ vᵢ`. There is a
permutation `σ` such that every partial sum `p_k = Σ_{i=1}^k v_{σ(i)}` satisfies
`p_k ≥ min(0, z) − dM·1`, where the minimum is componentwise.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 4.4, printed p. 18 (PDF p. 20).

**Formalization Note** The norm is the max norm, so "norm at most `M`" is `|vᵢ(j)| ≤ M` for all
coordinates `j`. Every partial sum means every `k ∈ [0, n]` (the empty sum included); the partial
sum of length `k` is the sum over the indices `i < k` of `Fin n`. The bound `M` is assumed
nonnegative: as printed, the statement fails for `n = 0`, `d ≥ 1`, `M < 0`. -/
theorem corollary_4_4 (d n : ℕ) (v : Fin n → Fin d → ℚ) (M : ℚ) (hM : 0 ≤ M)
    (hv : ∀ i j, |v i j| ≤ M) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : ℕ, k ≤ n → ∀ j : Fin d,
      min 0 (∑ i, v i j) - (d : ℚ) * M ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), v (σ i) j := by sorry

end VAS5Reach
