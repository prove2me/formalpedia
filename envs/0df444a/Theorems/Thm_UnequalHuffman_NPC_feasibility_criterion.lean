-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_feasibility_criterion
-- name    : UnequalHuffman.NPC.feasibility_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:44:10.202904+00:00
-- url     : https://prove2.me/theorems/bb66ce26-9dfa-470c-ad4c-d6928bf38e09
-- title:
--   §2.2 (checking feasibility) — a leaf profile is realizable iff all I_t ≥ 0 and I_H = 0
-- statement:
--   For a leaf profile $(n_1,\dots,n_H)$ put $I_0 = 1$ and $I_t = 2I_{t-1} - n_t$ for $1 \le t \le H$. Some full ordered binary tree has exactly $n_t$ leaves at every depth $t$ and no other leaves if and only if $I_t \ge 0$ for all $0 \le t \le H$ and $I_H = 0$.
--
--   Source (p. 9): "Checking feasibility of the profile. Put $I_0 = 1$, $I_t = 2I_{t-1} - n_t$ $(1 \le t \le H)$. The profile is feasible if and only if every $I_t \ge 0$ and $I_H = 0$."
--
--   Differences from the source:
--   - generalization: a prescribed leaf profile (n1, …, nH) of the leaf-profile problem, with nH > 0 → any finite list [n1, …, nH] of naturals, nH = 0 allowed; reason: the criterion holds verbatim for every list; it specializes to profiles with nH > 0
--   - encoding: profile (n1, …, nH); internal counts I_t → n : List ℕ with n_t = n[t − 1]; I_t = intCount n t ∈ ℤ; reason: 0-based lists; integers so that a negative I_t is visible
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 9, §2.2 (unnumbered claim)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Trees

namespace UnequalHuffman.NPC

/-- §2.2, "Checking feasibility of the profile" (p. 9): with `I₀ = 1`, `I_t = 2 I_{t-1} - n_t`,
the leaf profile `(n₁, …, n_H)` is realized by a full ordered binary tree (exactly `n_t` leaves
at each depth `t` and no other leaves) iff every `I_t ≥ 0` and `I_H = 0`. -/
theorem feasibility_criterion (n : List ℕ) :
    ProfileFeasible n ↔ (∀ t ≤ n.length, 0 ≤ intCount n t) ∧ intCount n n.length = 0 := by sorry

end UnequalHuffman.NPC
