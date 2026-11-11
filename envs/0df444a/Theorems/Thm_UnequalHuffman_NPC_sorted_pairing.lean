-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_sorted_pairing
-- name    : UnequalHuffman.NPC.sorted_pairing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T05:43:34.461874+00:00
-- url     : https://prove2.me/theorems/e309ba15-1b6d-4557-9371-80401e6ddd57
-- title:
--   §2.2 (sorted pairing) — nonincreasing coefficients against sorted coordinates minimize the sum
-- statement:
--   Let $u_1 \ge u_2 \ge \dots \ge u_m$ be integers and $z_1,\dots,z_m$ integer coordinates (repetitions allowed). If the permutation $\pi$ sorts the coordinates nondecreasingly ($z_{\pi(1)} \le \dots \le z_{\pi(m)}$), then for every permutation $\sigma$
--   $$\sum_k u_k\, z_{\pi(k)} \;\le\; \sum_k u_k\, z_{\sigma(k)},$$
--   i.e. pairing the largest coefficient with the smallest coordinate minimizes the sum over all assignments of the coefficients to the leaves.
--
--   Source (p. 10): "For a fixed tree and depth, pairing the largest coefficient with the smallest coordinate minimizes the sum over all assignments of those coefficients to the leaves."
--
--   Differences from the source:
--   - generalization: coordinates of the leaves at one depth of a tree (natural numbers) → arbitrary integers z : Fin m → ℤ; reason: the inequality does not use the tree; it specializes to leaf coordinates
--   - encoding: the sorted pairing; all assignments of the coefficients to the leaves → u antitone in the rank k, a permutation π with z ∘ π monotone; all permutations σ of Fin m; reason: assignments of m coefficients to m leaves are the permutations
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 10, §2.2 (unnumbered claim)

import Mathlib

namespace UnequalHuffman.NPC

/-- §2.2, "Why the coefficient rows are nonincreasing" (p. 10): for nonincreasing coefficients
`u₁ ≥ ⋯ ≥ u_m` and coordinates `z`, the sorted pairing (the `k`-th largest coefficient with the
`k`-th smallest coordinate, i.e. `z ∘ π` nondecreasing) minimizes `∑_k u_k · z_{σ(k)}` over all
assignments `σ`, with signed coefficients and repeated coordinates allowed. -/
theorem sorted_pairing {m : ℕ} (u : Fin m → ℤ) (hu : Antitone u) (z : Fin m → ℤ)
    (π σ : Equiv.Perm (Fin m)) (hπ : Monotone (z ∘ π)) :
    ∑ k, u k * z (π k) ≤ ∑ k, u k * z (σ k) := by sorry

end UnequalHuffman.NPC
