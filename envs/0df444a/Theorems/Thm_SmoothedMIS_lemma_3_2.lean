-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_3_2
-- name    : SmoothedMIS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:22.826345+00:00
-- url     : https://prove2.me/theorems/b28bd66c-65f0-438c-a031-7b01a0693386
-- title:
--   Lemma 3.2 — a balanced partition of a two-hop neighbourhood
-- statement:
--   Let $F$ be a finite graph, $s\ge1$ an integer, and $Q\subseteq V(F)$ a nonempty set of seeds with $\deg_F(v)>s$ for every $v\in Q$. Let $Z=N^2_F[Q]$ and $z=|Z|$. Then $Z$ can be partitioned into sets $W_1,\dots,W_m$ such that
--   1. $s\le|W_i|\le 2s$ for every $i$, and hence $\dfrac{z}{2s}\le m\le\dfrac{z}{s}$;
--   2. any two vertices of the same part are joined by a path of length at most eight in $F[Z]$.
--
--   The parts are the vertices of the quotient graph in the proof of Lemma 3.1.
--
--   Differences from the source:
--   - encoding: F a graph → a finite graph on a Fintype vertex type; reason: all graphs of the paper are finite
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 3.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS

namespace SmoothedMIS

/-- **Lemma 3.2 (A balanced partition)** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed
Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 3.2, p.12). Let `F` be a
graph, `s ≥ 1` an integer, and `Q ⊆ V(F)` a nonempty set of seeds with `deg_F(v) > s` for every
`v ∈ Q`. Let `Z = N²_F[Q]` and `z = |Z|`. Then `Z` can be partitioned into `m` sets
`W_1, …, W_m` such that (i) `s ≤ |W_i| ≤ 2s` for every `i`, and hence `z/(2s) ≤ m ≤ z/s`; and
(ii) any two vertices of the same part are joined by a path of length at most eight in `F[Z]`.

**Formalization Note** `F` is a finite graph; (ii) is `(F.induce Z).edist u v ≤ 8`. -/
theorem lemma_3_2 {V : Type} [Fintype V] (F : SimpleGraph V) (s : ℕ) (hs : 1 ≤ s)
    (Q : Set V) (hQ : Q.Nonempty) (hdeg : ∀ v ∈ Q, s < deg F v) :
    ∃ (m : ℕ) (W : Fin m → Finset V),
      Pairwise (fun i j => Disjoint (W i) (W j)) ∧
      (∀ v, v ∈ twoHop F Q ↔ ∃ i, v ∈ W i) ∧
      (∀ i, s ≤ (W i).card ∧ (W i).card ≤ 2 * s) ∧
      ((twoHop F Q).ncard : ℝ) / (2 * s) ≤ m ∧ (m : ℝ) ≤ ((twoHop F Q).ncard : ℝ) / s ∧
      ∀ i, ∀ u v : twoHop F Q, u.1 ∈ W i → v.1 ∈ W i →
        (F.induce (twoHop F Q)).edist u v ≤ 8 := by sorry

end SmoothedMIS
