-- Prove2me | Theorems.Thm_PathORAMCap_lemma_4_12
-- name    : PathORAMCap.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:40.75921+00:00
-- url     : https://prove2.me/theorems/2882e71c-ade0-49ff-abc9-fd4acd37d013
-- title:
--   Lemma 4.12 — a coupling with a full scan of $2^L$ blocks: $S(\pi;s)\le D^{(4)}(A^*)$
-- statement:
--   Let $N\ge2$, $L=\lceil\log_2N\rceil$ and $\hat N=2^L$. Consider the execution $\pi=P_{4,N}(s,\alpha)$ for a fixed instance and the full scan $P_{4,\hat N}(\hat N,(1,\dots,\hat N))$ of $\hat N$ distinct addresses on the same tree, with final target-load vector $A^*$. The two executions can be built from shared random labels, each keeping its prescribed (uniform) distribution, so that
--
--   $$S(\pi;s)\le D^{(4)}(A^*)$$
--
--   for every realization of the shared labels.
--
--   This reduces every access sequence to the single canonical scan, whose labels have an explicit independent structure.
--
--   **Formalization Note** The shared construction is a nonempty finite set $\Omega'$ with maps to the label spaces of the two executions whose fibres all have the same size, so that the uniform law on $\Omega'$ pushes forward to the uniform law of each execution.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
--   - reading: Lemma 4.12 as printed (no bound on N) → 2 ≤ N; reason: §4.3 fixes N ≥ 2 throughout (p.16: "Throughout this subsection, fix an instance (s, α) of P4,N with N ≥ 2")
--   - encoding: two executions constructed from shared random labels, each retaining its prescribed distribution → a nonempty finite type Ω' with maps f, g to the two label spaces, every fibre of f and of g of equal size, and the inequality at every ω' ∈ Ω'; reason: equal fibres are exactly the condition that the uniform law on Ω' pushes forward to the uniform law of each execution; the paper's construction adds finitely many fresh uniform labels
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 4.12, p.19 (PDF p.22), eq. (23)

import Mathlib
import Definitions.Def_PathORAMCap_overflowAux
import Definitions.Def_PathORAMCap_targetLoads

set_option autoImplicit false

namespace PathORAMCap

/-- **Lemma 4.12** (Full-Scan Overflow Bounds the Actual Stash; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.19 (PDF p.22)): "Let
L = ⌈log2 N⌉ and N̂ = 2^L. Consider an execution π = P4,N(s, α) with a fixed access sequence α, and a
full scan of N̂ distinct addresses on the same tree. Let A∗ be the full scan's final target-load
vector. These two executions can be constructed using shared random labels, each retaining its
prescribed distribution, so that S(π; s) ≤ D(4)(A∗) (23) for every realization of the random labels
in this shared construction."

**Formalization Note.** §4.3's standing assumption `N ≥ 2` (p.16) is kept. The shared construction
is a nonempty finite uniform space `Ω'` with maps `f` to the labels of `π` and `g` to the labels of
the full scan `P_{4,N̂}(N̂, (1, …, N̂))`; "each retaining its prescribed distribution" is that every
fibre of `f` and of `g` has the same size (`card Ω' = card(target) · |fibre|`), so both push the
uniform law forward to the uniform law. The inequality holds for every `ω' ∈ Ω'`. -/
theorem lemma_4_12 (N : ℕ) (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s) (α : Fin s → Fin N) :
    ∃ (Ω' : Type) (_ : Fintype Ω'), Nonempty Ω' ∧
      ∃ (f : Ω' → Labels N s) (g : Ω' → Labels (2 ^ treeDepth N) (2 ^ treeDepth N)),
        (∀ ω : Labels N s, Fintype.card Ω' =
          Fintype.card (Labels N s) * (Finset.univ.filter (fun ω' => f ω' = ω)).card) ∧
        (∀ ω : Labels (2 ^ treeDepth N) (2 ^ treeDepth N), Fintype.card Ω' =
          Fintype.card (Labels (2 ^ treeDepth N) (2 ^ treeDepth N)) *
            (Finset.univ.filter (fun ω' => g ω' = ω)).card) ∧
        ∀ ω' : Ω', (stashSize 4 α (f ω') s : ℝ) ≤
          overflowD 4 (treeDepth (2 ^ treeDepth N))
            (targetLoads (fun i => i) (g ω') (2 ^ treeDepth N)) := by sorry

end PathORAMCap
