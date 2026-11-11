-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_19
-- name    : WeakStrongMSR.lemma_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:25:43.892702+00:00
-- url     : https://prove2.me/theorems/0974be44-1fe0-415d-9f89-9d92fdb014b3
-- title:
--   Lemma 3.19 — components: at most $m$, $B^\prime_J\subseteq B_J$, $\sum_JR_J=14\sum_iR_i$
-- statement:
--   Let $d$ be a metric, let $s_1,\dots,s_m$ be points, and let $R_1,\dots,R_m\ge0$. Consider the graph on $\{1,\dots,m\}$ with an edge $ij$ when $d(s_i,s_j)\le 7(R_i+R_j)$.
--
--   1. The graph has at most $m$ connected components.
--   2. Let $J$ be a component and $i_0\in J$ any root. For every $i\in J$ and every $x$ with $d(s_i,x)\le 5R_i$,
--   $$d(s_{i_0},x)\le R_J:=14\sum_{j\in J}R_j .$$
--   That is, $B'_J=\bigcup_{i\in J}B(s_i,5R_i)\subseteq B(c_J,R_J)$.
--   3. $\displaystyle\sum_J 14\sum_{i\in J}R_i=14\sum_{i=1}^mR_i$.
--
--   This is the geometric step that turns the selected candidates into $O(k)$ balls of total radius $O(k\lambda)$.
--
--   Differences from the source:
--   - generalization: "Choose any one c_J" as root → the inclusion is stated for every root of the component; reason: covers the root chosen by the algorithm
--   - encoding: components J → the set of indices reachable from the root (clause 2) and Mathlib connected components (clauses 1, 3); reason: same components
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.19, p.18 (PDF 19)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.19** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.18, PDF p.19).
"There are at most m graph components, and for each component J, B′_J ⊆ B_J. Moreover,
∑_J R_J = 14 ∑_{i=1}^m R_i."

Let `d` be a metric, `s_1, …, s_m` points and `R_1, …, R_m ≥ 0`, and let `G` be the graph on
`{1, …, m}` with an edge `ij` when `d(s_i, s_j) ≤ 7(R_i + R_j)`. Then
1. `G` has at most `m` connected components;
2. for every component `J`, every choice of root `i₀ ∈ J`, every `i ∈ J` and every `x` with
   `d(s_i, x) ≤ 5R_i`: `d(s_{i₀}, x) ≤ R_J = 14 ∑_{j ∈ J} R_j` (that is, `B′_J ⊆ B_J`);
3. `∑_J 14 ∑_{i ∈ J} R_i = 14 ∑_i R_i`.

**Formalization Note.** The component of the root `i₀` is the set of indices reachable from
`i₀`; the statement holds for every root (the paper chooses "any one"). -/
theorem lemma_3_19 {n m : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d)
    (s : Fin m → Fin n) (R : Fin m → ℝ) (hR : ∀ i, 0 ≤ R i) :
    Nat.card (SimpleGraph.fromRel (fun i j : Fin m => d (s i) (s j) ≤ 7 * (R i + R j))).ConnectedComponent
        ≤ m ∧
    (∀ i₀ i : Fin m,
      (SimpleGraph.fromRel (fun i j : Fin m => d (s i) (s j) ≤ 7 * (R i + R j))).Reachable i₀ i →
      ∀ x : Fin n, d (s i) x ≤ 5 * R i →
        d (s i₀) x ≤ 14 * ∑ j ∈ Finset.univ.filter (fun j =>
          (SimpleGraph.fromRel (fun i j : Fin m => d (s i) (s j) ≤ 7 * (R i + R j))).Reachable i₀ j),
          R j) ∧
    ∑ J ∈ Finset.univ.image
        (SimpleGraph.fromRel (fun i j : Fin m => d (s i) (s j) ≤ 7 * (R i + R j))).connectedComponentMk,
      14 * ∑ i ∈ Finset.univ.filter (fun i =>
        (SimpleGraph.fromRel (fun i j : Fin m => d (s i) (s j) ≤ 7 * (R i + R j))).connectedComponentMk i
          = J), R i
      = 14 * ∑ i, R i := by sorry

end WeakStrongMSR
