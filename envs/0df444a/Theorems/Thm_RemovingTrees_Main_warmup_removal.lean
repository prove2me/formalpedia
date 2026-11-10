-- Prove2me | Theorems.Thm_RemovingTrees_Main_warmup_removal
-- name    : RemovingTrees.Main.warmup_removal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:20.475572+00:00
-- url     : https://prove2.me/theorems/401e83cd-b8c6-4458-9392-5d36d1b86c33
-- title:
--   Lemma 3.3 — Efficient tree removal and removal of C packed trees
-- statement:
--   Let $G$ be a connected finite undirected multigraph on at least two vertices and put $k=\lambda(G)$. A uniform polynomial-time bit machine returns a spanning tree $T$ such that
--   $$
--   \lambda(G-T)\ge\frac34 k-67.
--   $$
--   For every positive integer $C\le\lfloor k/2\rfloor$, the same machine, on the general-clause request, returns a subgraph $G'$ that is the union of $C$ edge-disjoint spanning trees, together with a residual packing witnessing
--   $$
--   \lambda(G-G')\ge\frac34 k-67C,\qquad
--   G-G'\text{ contains at least }\lfloor k/2\rfloor-44C\text{ edge-disjoint spanning trees}.
--   $$
--   Both clauses include every connected graph, without a parity restriction or the extra restriction $44C\le\lfloor k/2\rfloor$. This is the constructive initialization used by the improvement iteration.
--
--   **Formalization Note** Input $C=0$ selects the first clause; positive $C$ selects the second. It does not assert a zero-tree version in place of the first conclusion. The packing lower bound is an integer comparison.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
--   - encoding: polynomial-time construction → one finite machine and one polynomial before all inputs, with halting and actual encoded output correctness; reason: makes the computational clause explicit in the framed binary input model
--   - encoding: possibly negative number of residual packed trees → integer lower bound on the length of an explicitly returned nonnegative packing; reason: avoids natural subtraction underflow and preserves the source lower bound
--   - encoding: two constructive conclusions → one request-tagged program, using C = 0 for the single-tree clause and positive C for the general clause; reason: both source clauses remain present in one theorem and one finite program can dispatch between them
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Lemma 3.3, p.5

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Lemma 3.3, p.5: C=0 requests its first clause, positive C the general clause.
No parity restriction is made. -/
theorem warmup_removal :
    ∃ M : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
    ∀ (n m : ℕ) (G : MultiGraph n m) (k C : ℕ),
      2 ≤ n → Connected G Finset.univ → k = connectivity G Finset.univ →
      (C = 0 ∨ (0 < C ∧ C ≤ k / 2)) →
      BitResult M a d (encGraph G ++ encNat k ++ encNat C) (WarmupOutput G k C) := by sorry
end RemovingTrees.Main
