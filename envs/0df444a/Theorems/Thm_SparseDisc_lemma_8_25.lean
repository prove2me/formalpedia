-- Prove2me | Theorems.Thm_SparseDisc_lemma_8_25
-- name    : SparseDisc.lemma_8_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:48.164486+00:00
-- url     : https://prove2.me/theorems/93a4003a-cd2e-4c16-bf5e-0cbce4a2dc1a
-- title:
--   Lemma 8.25 — near-dichotomy
-- statement:
--   Let $S \ne \emptyset$ be finite and let $\{\pm1\}^S = P \sqcup W \sqcup N$ be a partition with $\operatorname{dist}(P, N) \ge 2$. If $W$ contains no near-loop, then $P$ or $N$ is near-thick.
--
--   Together with the near-cover lemma it gives the lossless transfer of Corollary 8.28.
--
--   **Formalization Note** The partition is stated as pairwise disjointness of $P, W, N$ together with $P \cup W \cup N = \{\pm1\}^S$; $\operatorname{dist}(P, N) \ge 2$ is $\operatorname{dist}(p, q) \ge 2$ for all $p \in P$, $q \in N$.
--
--   Differences from the source: none.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 8.25, p.40

import Mathlib
import Definitions.Def_SparseDisc_IsNearThick

namespace SparseDisc

/-- **Lemma 8.25 (near-dichotomy)** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.40). Let `S ≠ ∅` and
`{±1}^S = P ⊔ W ⊔ N` with `dist(P, N) ≥ 2`. If `W` contains no near-loop, then `P` or `N` is
near-thick.

**Formalization Note** `P ⊔ W ⊔ N` is a partition: pairwise disjoint with union the whole cube.
`dist(P, N) ≥ 2` is `dist(p, q) ≥ 2` for all `p ∈ P`, `q ∈ N`. -/
theorem lemma_8_25 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (P W N : Set (Cube S)) (hPW : Disjoint P W) (hWN : Disjoint W N) (hPN : Disjoint P N)
    (hcov : P ∪ W ∪ N = Set.univ) (hdist : ∀ p ∈ P, ∀ q ∈ N, 2 ≤ hammingDist p q)
    (hW : ¬ HasNearLoop W) :
    IsNearThick P ∨ IsNearThick N := by sorry

end SparseDisc
