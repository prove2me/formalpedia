-- Prove2me | Theorems.Thm_SkewMatching_lemma_23_pause_progress
-- name    : SkewMatching.lemma_23_pause_progress
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:21.295798+00:00
-- url     : https://prove2.me/theorems/73f32c1c-b25c-447f-b086-b3c2c0194ba2
-- title:
--   Lemma 23 (i)–(ii) — pauses and progress of the resumable search (running-time clauses carried by Theorem 1)
-- statement:
--   Let $G$ be a finite skew-symmetric graph and $s$ a vertex.
--
--   1. For every $\sigma$-closed $H_0$, either $H_0$ has a regular $s$–$s'$ path, or the search reaches a first pause on $H_0$ from the partition $A=\{s\}$, $A'=\{s'\}$, $k=0$ by Grow and Merge.
--   2. For every pause $(H,P)$ of the search and every $\sigma$-closed $H'\supseteq H$, either $H'$ has a regular $s$–$s'$ path, or a finite sequence of Grow and Merge leads from $P$ to a barrier of $H'$ whose $A\cup X_1\cup\dots\cup X_k$ is the set of vertices regularly reachable from $s$ in $H'$.
--   3. If $P$ is still a barrier of $H'$, that is, no inserted pair violates it, then $P$ is already a pause of $H'$, so the search need not resume.
--
--   This is what lets the algorithm stop at each barrier and continue after inserting edges, without undoing any earlier step. The paper only sketches it, following Goldberg and Karzanov. It implies that reachability policies exist.
--
--   Differences from the source:
--   - reading: there is an algorithm with guarantees (i), (ii) → the search can always continue from each pause in the stated way; a ReachPolicy exists by choice; reason: the time-free content of an algorithm statement is the existence of its continuation
--   - reading: O(1) time per pair and total time Õ(m) → not in this item; carried by the goal theorem_1; reason: a time clause needs a machine and data structures, and the title marks the split (decision 11)
--   - encoding: a skew-symmetric graph H → a σ-closed edge set of a finite SkewGraph; reason: a σ-closed edge set is itself a skew-symmetric multigraph
--   - encoding: a path → a vertex-simple path; reason: a regular walk contains a vertex-simple regular path, so existence is unchanged
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 23, pp.15–16 ('we only sketch it')

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_GMStep

namespace SkewMatching

/-- **Lemma 23 (i)–(ii)**, pp.15–16: the pauses and the progress of the resumable regular reachability search. The running-time clauses ("`O(1)` time per pair", "`Õ(m)`") are carried by the goal, Theorem 1.

(i) "Whenever the algorithm pauses, it has found a barrier (A, A′, X₁, …, X_k, M) of the current H and A ∪ X₁ ∪ ⋯ ∪ X_k is the set of vertices reachable from s by regular paths in H. While symmetric edge pairs are inserted,
the algorithm … only resumes the search when some inserted pair violates the current barrier." (ii) "The algorithm maintains a partition (A, A′, X₁, …, X_k, M) which initially has A = {s}, A′ = {s′} and k = 0. Between each
resume and pause, the partition changes only through the following two operations": Grow and Merge.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 23, pp.15–16 ("we only sketch it").

**Formalization Note.** The lemma asserts an algorithm; its content apart from time is that the search can always continue in this way. So: from an initial `σ`-closed `H₀`, the search outputs a regular `s`–`s′` path or reaches a first pause;
from every pause `(H, P)` and every `σ`-closed `H′ ⊇ H`, it outputs a regular path in `H′` or reaches, by Grow and Merge from `P`, a pause of `H′`; and a pair that does not violate `P` leaves `P` a pause. By choice, these give a `ReachPolicy`. -/
theorem lemma_23_pause_progress {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (s : V) :
    (∀ H₀ : Finset E, G.SymmClosed H₀ →
      (∃ p, G.IsRegularPathIn H₀ s (G.σV s) p) ∨ ∃ P, G.Paused s H₀ P) ∧
    ∀ (H H' : Finset E) (P : Partition V), G.Paused s H P → H ⊆ H' → G.SymmClosed H' →
      ((∃ p, G.IsRegularPathIn H' s (G.σV s) p) ∨ ∃ P', G.GMSeq H' P P' ∧ G.IsPause H' s P') ∧
        (G.IsBarrier H' s P → G.IsPause H' s P) := by sorry

end SkewMatching
