-- Prove2me | Theorems.Thm_PathORAMCap_proposition_4_3
-- name    : PathORAMCap.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:23.46518+00:00
-- url     : https://prove2.me/theorems/3137c6da-779c-4561-ba99-037498c2ca8a
-- title:
--   Proposition 4.3 — $\mathbb E[u^{S(\pi;s)}]\le\mathbb E[u^{Q_{L+1}}]$ for $1<u<2$, $N\ge2$
-- statement:
--   For every integer $N\ge2$, every instance $(s,\alpha)$ of $P_{4,N}$ and every $1<u<2$, with $\pi=P_{4,N}(s,\alpha)$ and $L=\lceil\log_2N\rceil$,
--
--   $$\mathbb E\bigl[u^{S(\pi;s)}\bigr]\le\mathbb E\bigl[u^{Q_{L+1}}\bigr],$$
--
--   where $Q_{L+1}$ is the root overflow, with capacity four, of an independent geometric-load tree of height $L+1$.
--
--   The dependent real node loads are thus dominated, in exponential moment, by independent ones, whose overflow can be analysed recursively.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
--   - encoding: Q_h, the root overflow of an independent geometric-load tree of height h (Definition 4.2) → QLaw Z h : PMF ℕ, defined by the law recursion (16)/(48) from Q_0 = 0; reason: the recursion, stated in the paper, determines the law uniquely; every statement involves Q_h only through its law
--   - encoding: moments and means of Q_h as real numbers → tsums in ℝ≥0∞; reason: they may be infinite in general, and ℝ≥0∞ needs no summability side condition; the stated bounds are finite values
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Proposition 4.3, p.15 (PDF p.18), eq. (17)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST
import Definitions.Def_PathORAMCap_QLaw

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Proposition 4.3** (Comparison with Geometric Loads; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.15 (PDF p.18)): "For every integer
N ≥ 2, every instance (s, α) of P4,N, and every 1 < u < 2, write π = P4,N(s, α) and L = ⌈log2 N⌉.
Then E[u^S(π;s)] ≤ E[u^Q_{L+1}]. (17)"

**Formalization Note.** The left side is the uniform average over the labels (a real number); the
right side is the moment of `Q_{L+1} = Q^(4)_{L+1}` in `ℝ≥0∞` (`QMoment`). -/
theorem proposition_4_3 (N : ℕ) (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s) (α : Fin s → Fin N)
    (u : ℝ) (hu1 : 1 < u) (hu2 : u < 2) :
    ENNReal.ofReal (mean (fun ω : Labels N s => u ^ stashSize 4 α ω s)) ≤
      QMoment 4 (treeDepth N + 1) u := by sorry

end PathORAMCap
