-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_2_3
-- name    : SparseCCE.ThreePlayer.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:05:18.102982+00:00
-- url     : https://prove2.me/theorems/61ac503e-2282-4d3a-91a7-46f646210e9c
-- title:
--   Lemma 2.3 — a $T$-sparse distribution has two-player marginals of rank at most $T$
-- statement:
--   Let $\mu$ be a $T$-sparse distribution on the action profiles of a normal-form game (finite players, finite action sets). Then for all players $i\neq k$, the real matrix $\mu_{ik}$ (rows $B_i$, columns $B_k$) has rank at most $T$.
--
--   Differences from the source: none.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 2.3, p. 13.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm

namespace SparseCCE.ThreePlayer

/-- **Lemma 2.3 (Sparsity bounds rank)**, p. 13: if `μ` is `T`-sparse, then `rank μ_{ik} ≤ T` for
all players `i ≠ k`. -/
theorem lemma_2_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ j, Fintype (B j)]
    [∀ j, DecidableEq (B j)] (T : ℕ) (μ : ((j : ι) → B j) → ℝ) (hμ : IsTSparse T μ) :
    ∀ i k : ι, i ≠ k → (pairMarginal μ i k).rank ≤ T := by sorry

end SparseCCE.ThreePlayer
