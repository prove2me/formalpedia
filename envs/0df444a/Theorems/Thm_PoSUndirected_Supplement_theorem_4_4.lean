-- Prove2me | Theorems.Thm_PoSUndirected_Supplement_theorem_4_4
-- name    : PoSUndirected.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:34:27.224207+00:00
-- url     : https://prove2.me/theorems/4d7400c8-0730-4a66-a0c8-c4d5f5ef59f5
-- title:
--   Theorem 4.4 — rank-four boundary at costs $724$ and $1449$
-- statement:
--   There is a finite subdivision of $K_{3,3}$ with 17 physical edges and one endpoint owner per edge, positive real costs, and maximum physical block rank exactly four, for which an optimum costs $724$ and the unique weak equilibrium costs $1449$. Its ordinary price of stability is therefore
--   $$
--   \frac{1449}{724}>2.
--   $$
--   No endpoint-owner instance with an arbitrary nonempty owned subset and maximum block rank at most three has price of stability above two. Consequently four is the least maximum block rank at which ordinary owner price of stability can exceed two.
--
--   Differences from the source:
--   - encoding: a subdivision of $K_{3,3}$ → six distinct branch vertices and nine edge-disjoint branch paths with pairwise disjoint internal vertices, covering every physical edge; reason: the standard subdivision definition, retaining distinct parallel physical edges
--   - encoding: maximum block rank four → rank at most four together with a physical block satisfying $|E(B)|+1=|V(B)|+4$; reason: subtraction-free exact cycle rank on a connected block
--   - encoding: four is the least maximum block rank permitting ordinary owner PoS above two → a rank-four witness with OrdinaryPoSValue 1449/724 and a universal q≤2 clause for every rank-at-most-three nonempty owned subset; reason: direct logical expansion of the least-rank conclusion over the same owner class
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 4.4, p.8 (PDF p.10); explicit construction, Appendix B.10

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_OwnerRankClassSupremum

open CongestionPoA.AsymSum

set_option autoImplicit false

namespace PoSUndirected.Supplement

/-- **Theorem 4.4 (rank-four boundary).** Tsoufis, preprint sha256 c095d811…, p.8
(PDF p.10); explicit construction, Appendix B.10.

There is a 17-edge subdivision of `K₃,₃`, fully endpoint-owned, of maximum physical block rank
four, with optimum cost `724` and one unique weak equilibrium of cost `1449`.  No endpoint-owner
instance with any nonempty owned subset and maximum block rank at most three has ordinary PoS above
two, so four is the least possible maximum block rank.

**Formalization Note.** `IsSubdivisionK33` retains six distinct branch vertices and nine internally
vertex-disjoint physical paths; parallel physical edges remain separately labelled. -/
theorem theorem_4_4 :
    (∃ I : OwnerRealInstance,
      I.nE = 17 ∧ I.owned = Finset.univ ∧ I.Valid 4 ∧ MaximumBlockRankEq I.ends 4 ∧
      IsSubdivisionK33 I.ends ∧
      ∃ (O N : {e : Fin I.nE // e ∈ I.owned} → Finset (Fin I.nE)),
        IsSocialOptimum I.game I.c O ∧ socialCost I.c O = 724 ∧
        IsPureNash I.game N ∧ socialCost I.c N = 1449 ∧
        (∀ Q, IsPureNash I.game Q → Q = N) ∧
        OrdinaryPoSValue I.game I.c ((1449 : ℝ) / 724)) ∧
    (∀ (I : OwnerRealInstance) (q : ℝ), I.Valid 3 →
      OrdinaryPoSValue I.game I.c q → q ≤ 2) := by sorry

end PoSUndirected.Supplement
