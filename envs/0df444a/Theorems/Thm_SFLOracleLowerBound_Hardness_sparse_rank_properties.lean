-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_sparse_rank_properties
-- name    : SFLOracleLowerBound.Hardness.sparse_rank_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:28:10.495205+00:00
-- url     : https://prove2.me/theorems/2f9e5a5c-3b44-4e3a-93cb-284484db6dcf
-- title:
--   Lemma 23 — Properties of the sparse rank function
-- statement:
--   For $d\ge4$, $K=d^{d+3}$, $m=K^2$, and a matching-decomposed base graph satisfying (12), the constructed sparse function $\rho$ is a genuine matroid rank function on the entire lifted client set. It also satisfies
--   $$\rho(N_{\widetilde G}(\{\widetilde v\}))\le3,\qquad \rho(U+a)=\rho(U)$$
--   for every lifted right vertex $\widetilde v$, lifted client set $U$ and cyclic shift $a$.
--
--   These conclusions establish rank validity, cheap neighborhoods and shift invariance for the specific sparse witness construction. Rank validity is not assumed.
--
--   Differences from the source:
--   - encoding: two disjoint sides of size m and matching colours in ℤ_d → each side is indexed by Fin m, with its side distinguished in a sum, and cyclic colours by Fin d; reason: these are finite coordinate choices; every coloured edge, including repeated endpoints, is retained
--   - encoding: integer witness cost Φ and nonnegative rank ρ → Φ and the capped minimum are calculated in ℤ, with nonnegativity obtained from local expansion; reason: integer subtraction retains negative intermediate values and changes no value under the source assumptions
--   - generalization: the base graph of Lemma 19 for sufficiently large d, including its large-cover property → any matching-decomposed graph with m=(d^(d+3))², d≥4 and expansion (12); reason: the proofs use expansion and the displayed cap, not the large-cover bound; they work for every d≥4, so include all sufficiently large source instances
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 23, p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SparseRank

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 23, p.23. Rank validity is a conclusion. -/

theorem sparse_rank_properties (d : ℕ) (hd : 4 ≤ d)
    (M : MatchingGraph d (graphSize d)) (hexp : BaseExpansion M (graphCap d)) :
    MatroidRank (sparseRankReal M (graphCap d)) ∧
    (∀ v : Fin (graphSize d) × Fin d, sparseRank M (graphCap d) (liftNeighbors M {v}) ≤ 3) ∧
    (∀ U : Finset (Fin (graphSize d) × Fin d), ∀ a : Fin d,
      sparseRank M (graphCap d) (shiftSet U a) = sparseRank M (graphCap d) U) := by sorry

end SFLOracleLowerBound.Hardness
