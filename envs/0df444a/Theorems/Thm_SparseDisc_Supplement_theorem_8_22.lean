-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_8_22
-- name    : SparseDisc.Supplement.theorem_8_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:14:19.797194+00:00
-- url     : https://prove2.me/theorems/db4e53bd-9413-4450-9378-f4d951d8efca
-- title:
--   Theorem 8.22 — four leveled-graph goodness criteria
-- statement:
--   Let $(G,\ell)$ be a finite leveled graph with positive integer levels.
--
--   1. A forest is good when no two level-$1$ vertices are adjacent.
--   2. If $G$ is triangle-free, no vertex has two neighbours on a cycle avoiding it, and each block contains at most one level-$1$ vertex, then $(G,\ell)$ is good. Consequently such graphs are $2$-good; this includes triangle-free outerplanar graphs, triangle-free graphs in which no vertex has two neighbours of degree at least $3$, and graphs obtained by subdividing every edge of a simple graph at least twice.
--   3. If vertices in $D$ are pairwise nonadjacent and have no common neighbour, $G-D$ is a forest, and $N(D)$ is independent, then $G$ is $2$-good.
--   4. Let $C\ge2$ and $V=V_1\sqcup V_2$. If $V_1$ has an ordering with at most $C-1$ later neighbours in $V_1$, each $v\in V_2$ has $q_v\le C-1$ neighbours in $V_1$, and the induced leveled graph on $V_2$ with level $C-q_v$ is good, then $G$ is $C$-good.
--
--   These clauses preserve the non-uniform levels and every named graph class in the source.
--
--   Differences from the source:
--   - encoding: forest, triangle-free, cycles avoiding a vertex and block level counts → Mathlib acyclicity and clique-freeness, cycle walks whose support avoids the vertex, and finite filters over the published block predicate; reason: standard finite simple-graph encodings of the source conditions
--   - encoding: $V=V_1\sqcup V_2$ and the level $C-q_v$ → disjoint finite vertex sets covering `univ`, with the induced subtype graph on $V_2$ and natural level subtraction guarded by $q_v\le C-1$; reason: Lean encoding preserves positivity and the exact non-uniform levels
--   - encoding: graphs obtained by subdividing each edge at least twice → isomorphism to the published subdivision construction with at least two inserted vertices per original edge; reason: Lean convention, same graph class
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.22, p.38

import Mathlib
import Definitions.Def_SparseDisc_IsLevelGood
import Definitions.Def_SparseDisc_IsCGood
import Definitions.Def_SparseDisc_IsBlock
import Definitions.Def_TaitTobin_Outerplanar_Setting
import Definitions.Def_SparseDisc_Supplement_IsSubdivisionAtLeastTwice
import Definitions.Def_SparseDisc_Supplement_NoTwoNeighboursOnAvoidingCycle
import Definitions.Def_SparseDisc_Supplement_HasLaterBoundOn

namespace SparseDisc.Supplement

open Classical in
/-- **Theorem 8.22** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.38). All four leveled-graph goodness
criteria are stated, together with every graph-class consequence listed in part (b).

**Formalization Note** Forest means Mathlib `IsAcyclic`; triangle-free means `CliqueFree 3`.
Blocks are the published `SparseDisc.IsBlock`. In part (d), `V₁,V₂` are an explicit partition,
`q_v` is the number of neighbours of `v` in `V₁`, and the induced graph on `V₂` carries the
non-uniform level `C-q_v`. -/
theorem theorem_8_22 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ℓ : V → ℕ),
      (∀ v, 1 ≤ ℓ v) → (∀ u v, G.Adj u v → ¬ (ℓ u = 1 ∧ ℓ v = 1)) →
      G.IsAcyclic → SparseDisc.IsLevelGood G ℓ) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ℓ : V → ℕ),
      (∀ v, 1 ≤ ℓ v) → G.CliqueFree 3 → NoTwoNeighboursOnAvoidingCycle G →
      (∀ W : Finset V, SparseDisc.IsBlock G W →
        (W.filter (fun v => ℓ v = 1)).card ≤ 1) → SparseDisc.IsLevelGood G ℓ) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.CliqueFree 3 → NoTwoNeighboursOnAvoidingCycle G → SparseDisc.IsCGood G 2) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.CliqueFree 3 → TaitTobin.Outerplanar.IsOuterplanar G → SparseDisc.IsCGood G 2) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.CliqueFree 3 →
      (∀ v, (Finset.univ.filter (fun w => G.Adj v w ∧ 3 ≤ G.degree w)).card ≤ 1) →
      SparseDisc.IsCGood G 2) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsSubdivisionAtLeastTwice G → SparseDisc.IsCGood G 2) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (D : Finset V),
      (∀ u ∈ D, ∀ v ∈ D, u ≠ v →
        ¬ G.Adj u v ∧ ¬ ∃ w, G.Adj u w ∧ G.Adj v w) →
      (G.induce ({v | v ∉ D} : Set V)).IsAcyclic →
      (∀ u v, (∃ d ∈ D, G.Adj d u) → (∃ d ∈ D, G.Adj d v) →
        G.Adj u v → False) → SparseDisc.IsCGood G 2) ∧
    (∀ (C : ℕ), 2 ≤ C → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (V₁ V₂ : Finset V), Disjoint V₁ V₂ → V₁ ∪ V₂ = Finset.univ →
      HasLaterBoundOn G V₁ (C - 1) →
      (∀ v ∈ V₂, (V₁.filter (fun u => G.Adj v u)).card ≤ C - 1) →
      SparseDisc.IsLevelGood (G.induce (V₂ : Set V))
        (fun v => C - (V₁.filter (fun u => G.Adj v.1 u)).card) →
      SparseDisc.IsCGood G (C : ℝ)) := by sorry

end SparseDisc.Supplement
