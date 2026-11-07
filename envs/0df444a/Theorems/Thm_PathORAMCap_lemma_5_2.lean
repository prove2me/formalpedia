-- Prove2me | Theorems.Thm_PathORAMCap_lemma_5_2
-- name    : PathORAMCap.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:43.688196+00:00
-- url     : https://prove2.me/theorems/93df4e0b-70c6-4fca-86c1-2ab2c76416c1
-- title:
--   Lemma 5.2 — $S(\pi;s)\ge\sum_{|v|=d}F_v-Z(2^d-1)$ for retained local overflows
-- statement:
--   Fix an instance $(s,\alpha)$, the execution $\pi=P_{Z,N}(s,\alpha)$ and a depth $d$ of its tree. For each node $v$ at depth $d$ retain any subset of the targets in its subtree, and let $W_v$ be the root overflow of this retained field on the subtree of $v$. For any quantities $0\le F_v\le W_v$,
--
--   $$S(\pi;s)\ge\sum_{|v|=d}F_v-Z(2^d-1).$$
--
--   The inequality holds for each realization, hence also for random retained fields and random $F_v$. It turns local surpluses of disjoint regions into a lower bound on the stash, without any independence between the regions.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
--   - encoding: "retain any subset of targets in its subtree" → a set T v of created blocks whose final target d_s(b) satisfies v ⪯ d_s(b); W_v is the overflow above v of their target counts on the L − d + 1 levels of the subtree; reason: a retained target is a block's target in the subtree; this is every such retained field
--   - encoding: the inequality for each realization and hence for random choices → the inequality for each realization ω and all retained sets and F; reason: a random choice is a choice at each realization, so the second sentence is the first applied pointwise
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 5.2, p.38 (PDF p.41), eq. (42)

import Mathlib
import Definitions.Def_PathORAMCap_overflowAux
import Definitions.Def_PathORAMCap_targetLoads

set_option autoImplicit false

namespace PathORAMCap

/-- **Lemma 5.2** (Aggregating Local Overflow; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.38 (PDF p.41)): "Fix an instance (s, α), the
execution π = PZ,N(s, α), and a depth d in its tree. For each node v at depth d, retain any subset of
targets in its subtree, and let Wv be the root overflow of this retained field. For any quantities
0 ≤ Fv ≤ Wv, S(π; s) ≥ Σ|v|=d Fv − Z(2^d − 1). (42) The inequality holds for each realization, and
hence also for random choices of the retained fields and the Fv."

**Formalization Note.** Stated for each realization `ω` (the random-choice sentence then follows
pointwise). The retained set `T v` consists of created blocks whose final target lies in the subtree
of `v`; `W_v` is the overflow above `v` of their target counts on the `L − d + 1` levels of that
subtree. -/
theorem lemma_5_2 (Z N s : ℕ) (hZ : 0 < Z) (hs : 1 ≤ s) (α : Fin s → Fin N)
    (ω : Labels N s) (d : ℕ) (hd : d ≤ treeDepth N) (T : Leaf d → Finset (Fin N))
    (hT : ∀ v b, b ∈ T v → IsCreated α s b ∧ v.toList <+: target α ω s b)
    (F : Leaf d → ℝ) (hF0 : ∀ v, 0 ≤ F v)
    (hFW : ∀ v, F v ≤ overflowAux Z (treeDepth N - d + 1)
      (fun w => (((T v).filter (fun b => target α ω s b = w)).card : ℝ)) v.toList) :
    ∑ v, F v - (Z : ℝ) * ((2 : ℝ) ^ d - 1) ≤ stashSize Z α ω s := by sorry

end PathORAMCap
