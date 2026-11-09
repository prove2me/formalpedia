-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_2_9
-- name    : ProportionalTSP.Exact.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:58.91902+00:00
-- url     : https://prove2.me/theorems/e9ef622f-ddb1-49e6-abe2-cc792b803fef
-- title:
--   Lemma 2.9 — Neighboring-load tree and both reassignment properties
-- statement:
--   For generic $w$, let $S\subseteq L$ and $u\in\mathbb N^L$ be supported on $S$ with $\sum_lu_l=k-1$. Then
--   $$T_S(u)=\bigcup_{j\in S}A_{u+e_j}$$
--   is a spanning tree on $S\sqcup R$, with degree $u_l+1$ at each $l\in S$. For each root $j\in S$, the first left vertex on the unique path from $r$ to $j$ is $A_{u+e_j}(r)$. For distinct $i,j\in S$, every vertex assigned to $i$ in $A_{u+e_j}$ remains assigned to $i$ in $A_{u+e_i}$, and exactly one additional right vertex is assigned to $i$ there. These statements apply to arbitrary feasible neighboring loads, including unbalanced ones.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
--   - encoding: the first S-vertex on the unique tree path from r to j → the parent of r when the tree is rooted at j; reason: the graph is bipartite and the asserted spanning-tree property makes these equivalent
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 2.9, PDF p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_2_9 {m k : ℕ} [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (w : Fin m → Fin k → ℝ) (hw : Generic w)
    (S : Finset (Fin m)) (u : Load m)
    (hsupp : ∀ l, l ∉ S → u l = 0) (hu : ∑ l, u l = k - 1) :
    (neighboringTree w S u).IsTree ∧
    (∀ l : S, (neighboringTree w S u).degree (.inl l) = u l.val + 1) ∧
    (∀ j : S, ∀ r : Fin k, ∃ l : S,
      canonical w (plusUnit u j.val) r = l.val ∧
      RootParent (neighboringTree w S u) (.inl j) (.inr r) (.inl l)) ∧
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∀ r, canonical w (plusUnit u j) r = i → canonical w (plusUnit u i) r = i) ∧
      ∃! r, canonical w (plusUnit u i) r = i ∧ canonical w (plusUnit u j) r ≠ i) := by sorry

end ProportionalTSP.Exact
