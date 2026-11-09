-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_2_7
-- name    : ProportionalTSP.Exact.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:58.82262+00:00
-- url     : https://prove2.me/theorems/31e966b5-8f3a-453b-a292-cf9fe465919c
-- title:
--   Lemma 2.7 — Bipartite Hamiltonian-cycle parity
-- statement:
--   Let $K$ be a finite simple bipartite graph with equal-sized parts $X,Y$, and assume every vertex in $X$ has degree three. For every edge $e$,
--   $$\#\{H:H\text{ is a Hamiltonian cycle of }K,\ e\in H\}\equiv0\pmod2.$$
--   In particular, every Hamiltonian cycle has a distinct companion. No degree constraint is imposed on $Y$. This parity result supports the optimal-tour structural theorem.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: Hamiltonian cycles counted as undirected cycles → finite unordered edge sets represented by a spanning simple cyclic list of length at least three; reason: rotations and reversal identify the same cycle, including in the parity count
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 2.7, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_2_7 (h : ℕ) (K : SimpleGraph (Vertex h h))
    (hbip : ∀ x y, K.Adj x y →
      (∃ l r, x = Sum.inl l ∧ y = Sum.inr r) ∨ (∃ l r, y = Sum.inl l ∧ x = Sum.inr r))
    (hdeg : ∀ x : Fin h, K.degree (.inl x) = 3) :
    (∀ e ∈ K.edgeSet, Even ((Finset.univ.filter (fun H : Finset (Sym2 (Vertex h h)) =>
      IsTour K H ∧ e ∈ H)).card)) ∧
    (∀ H, IsTour K H → ∃ H', IsTour K H' ∧ H' ≠ H) := by sorry

end ProportionalTSP.Exact
