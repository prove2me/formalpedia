-- Prove2me | Theorems.Thm_StrongPerfectGraph_Wonderful_roussel_rubio
-- name    : StrongPerfectGraph.Wonderful.roussel_rubio
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T14:43:33.958758+00:00
-- url     : https://prove2.me/theorems/4e832f80-cf65-4698-803c-9e897d10c613
-- title:
--   The Wonderful Lemma of Roussel and Rubio
-- statement:
--   **The Wonderful Lemma (Roussel–Rubio).** Let $G$ be a Berge graph (no odd hole and no odd antihole), let $X\subseteq V(G)$ be anticonnected (the complement graph induced on $X$ is connected), and let $P=v_0v_1\cdots v_k$ be an induced path of odd length $k$ in $G\setminus X$ whose ends $v_0,v_k$ are both complete to $X$. Then at least one of the following holds:
--
--   1. some edge $v_iv_{i+1}$ of $P$ is $X$-complete (both ends adjacent to every vertex of $X$);
--   2. $k\ge 5$ and $X$ contains a *leap* for $P$: nonadjacent $a,b\in X$ with $N(a)\cap V(P)=\{v_0,v_1,v_k\}$ and $N(b)\cap V(P)=\{v_0,v_{k-1},v_k\}$;
--   3. $k=3$ and there is an odd antipath from $v_1$ to $v_2$ with interior in $X$.
--
--   In the formalization $P$ is a list-based induced path with an even number of vertices, and the antipath is an induced path of the complement graph.
-- source:
--   M. Chudnovsky, A short proof of the Wonderful Lemma (2017), Theorem 1.2; M. Chudnovsky, N. Robertson, P. Seymour, R. Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), Theorem 2.1 (due to Roussel and Rubio).

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.Wonderful

open StrongPerfectGraph.Main

/-- **The Wonderful Lemma** (Roussel and Rubio; Theorem 1.2 of Chudnovsky's short proof, Theorem 2.1 of
Chudnovsky–Robertson–Seymour–Thomas). Let `G` be Berge, `X` an anticonnected set of vertices, and
`P = v₀ … v_k` an induced path with `k` odd (an even number of vertices), disjoint from `X`, whose two
ends are complete to `X`. Then (1) two consecutive vertices of `P` are both complete to `X`, or
(2) `k ≥ 5` and `X` contains a leap for `P` (nonadjacent `a, b ∈ X` with `N(a) ∩ P = {v₀, v₁, v_k}` and
`N(b) ∩ P = {v₀, v_{k-1}, v_k}`), or (3) `k = 3` and there is an odd antipath from `v₁` to `v₂` with
interior in `X`. -/
theorem roussel_rubio {V : Type*} {G : SimpleGraph V} (hG : IsBerge G) {X : Finset V}
    (hX : (Gᶜ.induce (X : Set V)).Connected) {P : List V} (hP : IsInducedPath G P)
    (hlen : Even P.length) (hdisj : ∀ v ∈ P, v ∉ X) {v0 vk : V} (h0 : P.head? = some v0)
    (hk : P.getLast? = some vk) (hv0 : ∀ x ∈ X, G.Adj v0 x) (hvk : ∀ x ∈ X, G.Adj vk x) :
    (∃ (i : ℕ) (u w : V), P[i]? = some u ∧ P[i + 1]? = some w ∧ (∀ x ∈ X, G.Adj u x) ∧
        (∀ x ∈ X, G.Adj w x)) ∨
    (6 ≤ P.length ∧ ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ ¬ G.Adj a b ∧
        (∀ (i : ℕ) (v : V), P[i]? = some v →
          (G.Adj a v ↔ (i = 0 ∨ i = 1 ∨ i + 1 = P.length))) ∧
        (∀ (i : ℕ) (v : V), P[i]? = some v →
          (G.Adj b v ↔ (i = 0 ∨ i + 2 = P.length ∨ i + 1 = P.length)))) ∨
    (P.length = 4 ∧ ∃ Q : List V, IsInducedPath Gᶜ Q ∧ Even Q.length ∧
        (∃ v1 v2, P[1]? = some v1 ∧ P[2]? = some v2 ∧ Q.head? = some v1 ∧
          Q.getLast? = some v2) ∧
        ∀ (i : ℕ) (v : V), Q[i]? = some v → 0 < i → i + 1 < Q.length → v ∈ X) := by sorry

end StrongPerfectGraph.Wonderful
