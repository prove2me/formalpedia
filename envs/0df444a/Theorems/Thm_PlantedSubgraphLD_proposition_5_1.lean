-- Prove2me | Theorems.Thm_PlantedSubgraphLD_proposition_5_1
-- name    : PlantedSubgraphLD.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:03.829605+00:00
-- url     : https://prove2.me/theorems/45770ade-e931-450b-a107-92ee8c972003
-- title:
--   Proposition 5.1 — low-interface edge decomposition of a connected graph of treewidth $\le k$
-- statement:
--   Let $k,\ell$ be positive integers and let $F$ be a finite connected graph with
--
--   $$
--   \mathrm{tw}(F)\le k\qquad\text{and}\qquad e(F)\ge\ell .
--   $$
--
--   Then $F$ admits an ordered edge decomposition $\mathcal T(F)=(T_1,\dots,T_m)$ such that
--
--   $$
--   \ell\le e(T_i)\le3\ell\quad(i=1,\dots,m),\qquad \mathrm{ov}(F,\mathcal T(F))\le(k+1)(m-1).
--   $$
--
--   Cutting along the bags of a tree decomposition, every cut costs at most $k+1$ shared vertices; this is the source of the $n^{(\mathrm{tw}+1)(m-1)}$ factor that the noise must beat in Lemma 4.6.
--
--   Differences from the source:
--   - encoding: tw(Γ), the minimum width of a tree decomposition → tw Γ := sInf {w | TreewidthLE Γ w} with the published RobertsonSeymour1986.GM5.TreewidthLE; reason: for a finite graph the set is nonempty and the infimum is attained; same value
--   - encoding: v(F) in ov(F, T(F)) = Σ v(Ti) − v(F) → the number of endpoints of edges of F (edgeSupp of the edge set); reason: F is connected with at least ℓ ≥ 1 edges, so every vertex is an endpoint of an edge
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Proposition 5.1, §5, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_ov
import Definitions.Def_PlantedSubgraphLD_tw

open Classical

namespace PlantedSubgraphLD

/-- **Proposition 5.1.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §5, Proposition 5.1, p.25 (PDF p.27): "Let k, ℓ be positive
integers, and let F be a connected graph satisfying tw(F) ≤ k and e(F) ≥ ℓ. Then F admits an
ordered edge decomposition T(F) = (T1, T2, . . . , Tm) such that ℓ ≤ e(Ti) ≤ 3ℓ for every
i = 1, 2, . . . , m, ov(F, T(F)) ≤ (k + 1)(m − 1)."

**Formalization Note** F is a finite simple graph on `V`; its ordered edge decomposition is one of
`E(F)` (`IsOrderedEdgeDecomp F.edgeFinset T`), and `ov` counts `v(F)` as the number of
endpoints of edges of `F`, which is `|V(F)|` since `F` is connected with at least `ℓ ≥ 1`
edges. -/
theorem proposition_5_1 (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) {V : Type} [Fintype V]
    [DecidableEq V] (F : SimpleGraph V) (hF : F.Connected) (htw : tw F ≤ k)
    (he : ℓ ≤ F.edgeFinset.card) :
    ∃ (m : ℕ) (T : Fin m → Finset (Sym2 V)), IsOrderedEdgeDecomp F.edgeFinset T ∧
      (∀ i, ℓ ≤ (T i).card ∧ (T i).card ≤ 3 * ℓ) ∧
      ov F.edgeFinset T ≤ ((k : ℤ) + 1) * ((m : ℤ) - 1) := by sorry

end PlantedSubgraphLD
