-- Prove2me | Theorems.Thm_SparseDisc_theorem_1_11
-- name    : SparseDisc.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:05.470194+00:00
-- url     : https://prove2.me/theorems/28bdb906-f9eb-4a59-a734-0ae15f3fb2f1
-- title:
--   Theorem 1.11 — antipodal blocking sets in the cube (Lemmas 8.12 and 8.13)
-- statement:
--   Let $S$ be a finite set with $|S| \ge 3$. Call $B \subseteq \{\pm1\}^S$ thick if every antipodal 1-path meets $B$.
--
--   1. Any two thick subsets of $\{\pm1\}^S$ are at Hamming distance at most $1$.
--   2. If $P, N \subseteq \{\pm1\}^S$ are at Hamming distance at least $3$ and $P \cup N$ is thick, then $P$ or $N$ is thick.
--
--   The distance $3$ cannot be replaced by $2$: for every finite $S$ with $|S|$ even and $|S| \ge 4$ there are $P, N \subseteq \{\pm1\}^S$ at Hamming distance at least $2$ such that $P \cup N$ is thick and neither $P$ nor $N$ is thick.
--
--   These two statements about a single cube are the content of the hub-transfer lemma (Lemma 8.15).
--
--   **Formalization Note** "At distance at most 1" is the existence of $b_1 \in B_1$, $b_2 \in B_2$ with $\operatorname{dist}(b_1, b_2) \le 1$; "at distance at least $k$" is $\operatorname{dist}(p, q) \ge k$ for all $p \in P$, $q \in N$, vacuous when one set is empty (the paper's $\operatorname{dist}(\cdot, \emptyset) = \infty$).
--
--   Differences from the source:
--   - generalization: the distance 3 cannot be replaced by 2 (some counterexample exists) → for every S with |S| even and |S| ≥ 4 there are P, N at distance ≥ 2 with P ∪ N thick and neither thick; reason: this is the family of examples given on p.33 (σ ≥ 2, σ = 0, σ ≤ −2); it specializes to the printed claim at |S| = 4
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.11, p.5; Lemmas 8.12, 8.13 and the example after them, p.33

import Mathlib
import Definitions.Def_SparseDisc_IsThick

namespace SparseDisc

/-- **Theorem 1.11** (antipodal blocking sets; Lemmas 8.12 and 8.13) (Zeng–Cao–Dai–Wang–Liao,
*Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), p.5; Lemmas 8.12, 8.13 and the example after them, p.33). Let `|S| ≥ 3`. (a) Any two
thick subsets of `{±1}^S` are at Hamming distance at most 1. (b) If `P, N ⊆ {±1}^S` are at Hamming
distance at least 3 and `P ∪ N` is thick, then `P` or `N` is thick. The distance 3 cannot be replaced
by 2: for every `S` with `|S|` even and at least 4 there are `P, N` at distance at least 2 with
`P ∪ N` thick and neither `P` nor `N` thick.

**Formalization Note** "At distance at most 1" is the existence of `b₁ ∈ B₁`, `b₂ ∈ B₂` with
`dist(b₁, b₂) ≤ 1`; "at distance at least 3" is `dist(p, q) ≥ 3` for all `p ∈ P`, `q ∈ N`
(vacuous if one is empty, matching `dist(·, ∅) = ∞`). The sharpness clause is stated for every even
`|S| ≥ 4`, the family of examples given on p.33. -/
theorem theorem_1_11 :
    (∀ (S : Type) [Fintype S] [DecidableEq S], 3 ≤ Fintype.card S →
      (∀ B₁ B₂ : Set (Cube S), IsThick B₁ → IsThick B₂ →
        ∃ b₁ ∈ B₁, ∃ b₂ ∈ B₂, hammingDist b₁ b₂ ≤ 1) ∧
      (∀ P N : Set (Cube S), (∀ p ∈ P, ∀ q ∈ N, 3 ≤ hammingDist p q) → IsThick (P ∪ N) →
        IsThick P ∨ IsThick N)) ∧
    (∀ (S : Type) [Fintype S] [DecidableEq S], 4 ≤ Fintype.card S → Even (Fintype.card S) →
      ∃ P N : Set (Cube S), (∀ p ∈ P, ∀ q ∈ N, 2 ≤ hammingDist p q) ∧ IsThick (P ∪ N) ∧
        ¬ IsThick P ∧ ¬ IsThick N) := by sorry

end SparseDisc
