-- Prove2me | Theorems.Thm_PathORAMCap_lemma_5_1
-- name    : PathORAMCap.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:31.156366+00:00
-- url     : https://prove2.me/theorems/12701acf-76f8-4f91-9812-10bd21444a1f
-- title:
--   Lemma 5.1 — $S(\pi;t)=D^{(Z)}(A(t))$; removing targets or raising $Z$ cannot increase overflow
-- statement:
--   For every positive integer $Z$, every instance $(s,\alpha)$ of $P_{Z,N}$ and every realization of its execution $\pi$,
--
--   $$S(\pi;t)=D^{(Z)}(A(t))\qquad(0\le t\le s),$$
--
--   where $A(t)$ is the target-load vector and $D^{(Z)}$ the root overflow of upward packing with capacity $Z$. Moreover, for fixed integer target loads $A$ on the tree:
--
--   1. removing targets cannot increase the root overflow: if $A'_v\le A_v$ at every node then $D^{(Z)}(A')\le D^{(Z)}(A)$;
--   2. increasing the bucket capacity cannot increase it: if $Z\le Z'$ then $D^{(Z')}(A)\le D^{(Z)}(A)$.
--
--   The identity replaces the refill dynamics by a static packing of targets, and the two monotonicity facts transfer bounds between capacities and between retained fields.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
--   - encoding: removing targets from a fixed target field → a pointwise smaller integer load vector on the nodes of the tree; reason: removing targets lowers each node's count and every pointwise smaller integer load vector arises this way
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 5.1, p.37 (PDF p.40)

import Mathlib
import Definitions.Def_PathORAMCap_overflowAux
import Definitions.Def_PathORAMCap_targetLoads

set_option autoImplicit false

namespace PathORAMCap

/-- **Lemma 5.1** (Packing Identity and Monotonicity; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.37 (PDF p.40)): "For every positive
integer Z, every instance (s, α) of PZ,N, and every realization of its execution π,
S(π; t) = D(Z)(A(t)) (0 ≤ t ≤ s). For fixed target loads, removing targets or increasing bucket
capacity cannot increase root overflow."

**Formalization Note.** Three conjuncts: the identity for every realization `ω` of the labels and
every `t ≤ s`; for integer loads `A' ≤ A` on the nodes of a depth-`L` tree, `D^(Z)(A') ≤ D^(Z)(A)`;
and `Z ≤ Z'` gives `D^(Z')(A) ≤ D^(Z)(A)`. Removing targets lowers the load vector pointwise. -/
theorem lemma_5_1 (Z : ℕ) (hZ : 0 < Z) :
    (∀ (N s : ℕ), 1 ≤ s → ∀ (α : Fin s → Fin N) (ω : Labels N s) (t : ℕ), t ≤ s →
        (stashSize Z α ω t : ℝ) = overflowD Z (treeDepth N) (targetLoads α ω t)) ∧
    (∀ (L : ℕ) (A' A : List Bool → ℕ), (∀ v : List Bool, v.length ≤ L → A' v ≤ A v) →
        overflowD Z L A' ≤ overflowD Z L A) ∧
    (∀ (Z' L : ℕ) (A : List Bool → ℕ), Z ≤ Z' → overflowD Z' L A ≤ overflowD Z L A) := by sorry

end PathORAMCap
