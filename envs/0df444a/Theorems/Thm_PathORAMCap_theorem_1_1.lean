-- Prove2me | Theorems.Thm_PathORAMCap_theorem_1_1
-- name    : PathORAMCap.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:06.525477+00:00
-- url     : https://prove2.me/theorems/77f641be-ceac-4023-b1bc-d0bf765104fd
-- title:
--   Theorem 1.1 — a uniform exponential stash tail bound holds if and only if $Z\ge4$
-- statement:
--   Fix a positive integer $Z$. The following statement holds if and only if $Z\ge4$: there exist constants $C\ge1$ and $c>0$, depending only on $Z$, such that for every integer $N\ge1$, every instance $(s,\alpha)$ of $P_{Z,N}$ and every integer $R\ge0$,
--
--   $$\mathbb P\bigl[S(P_{Z,N}(s,\alpha);s)>R\bigr]\le Ce^{-cR}.$$
--
--   Four is therefore the minimum bucket capacity of reliable Path ORAM with tree depth $\lceil\log_2N\rceil$: the uniform exponential stash tail bound of Definition 2.1 holds at every capacity $Z\ge4$ and fails at $Z=1,2,3$.
--
--   **Formalization Note** The bracketed statement is `HasUEST Z` (Definition 2.1), with $C,c$ chosen before $N$, the instance and $R$.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Theorem 1.1, p.8 (PDF p.11); informal version p.2 (PDF p.5)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST

set_option autoImplicit false

namespace PathORAMCap

/-- **Theorem 1.1** (Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.8 (PDF p.11); informal version p.2): "Fix a positive integer Z. The
following statement holds if and only if Z ≥ 4: there exist constants C ≥ 1 and c > 0, depending only
on Z, such that for every integer N ≥ 1, every instance (s, α) of PZ,N, and every integer R ≥ 0,
P[S(PZ,N(s, α); s) > R] ≤ Ce−cR."

**Formalization Note.** The bracketed statement is `HasUEST Z` (Definition 2.1): `C, c` precede
`N`, the instance and `R`; `P` is the uniform law on the labels; `S` is the stash after the last
refill of the process `P_{Z,N}` of §2.1 (`stashSize`). -/
theorem theorem_1_1 (Z : ℕ) (hZ : 0 < Z) : HasUEST Z ↔ 4 ≤ Z := by sorry

end PathORAMCap
