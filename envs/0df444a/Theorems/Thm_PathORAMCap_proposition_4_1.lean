-- Prove2me | Theorems.Thm_PathORAMCap_proposition_4_1
-- name    : PathORAMCap.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:18.531564+00:00
-- url     : https://prove2.me/theorems/5095e85c-b315-4dbb-b9f1-b170121acda1
-- title:
--   Proposition 4.1 — $\mathbb E[(7/5)^{S(\pi;s)}]\le 23/20$ for capacity four
-- statement:
--   For every integer $N\ge1$ and every instance $(s,\alpha)$ of $P_{4,N}$, the execution $\pi=P_{4,N}(s,\alpha)$ satisfies
--
--   $$\mathbb E\bigl[(7/5)^{S(\pi;s)}\bigr]\le\frac{23}{20}.$$
--
--   By Markov's inequality this exponential moment bound gives the tail bound of Theorem 1.2.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Proposition 4.1, p.14 (PDF p.17), eq. (14)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Proposition 4.1** (Uniform Stash Moment; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.14 (PDF p.17)): "For every integer N ≥ 1 and
every instance (s, α) of P4,N, let π = P4,N(s, α). Then E[(7/5)^S(π;s)] ≤ 23/20. (14)"

**Formalization Note.** `E` is the uniform average over the labels. -/
theorem proposition_4_1 (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : 1 ≤ s) (α : Fin s → Fin N) :
    mean (fun ω : Labels N s => (7 / 5 : ℝ) ^ stashSize 4 α ω s) ≤ 23 / 20 := by sorry

end PathORAMCap
