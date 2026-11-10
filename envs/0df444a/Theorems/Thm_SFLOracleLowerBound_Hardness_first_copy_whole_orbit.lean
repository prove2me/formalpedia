-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_first_copy_whole_orbit
-- name    : SFLOracleLowerBound.Hardness.first_copy_whole_orbit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:28:12.173051+00:00
-- url     : https://prove2.me/theorems/35b28684-5559-4fc0-b428-11f33ce486cb
-- title:
--   Lemma 25 — First copy and whole-orbit assignments
-- statement:
--   For the lifted instance with $d\ge4$, $K=d^{d+3}$, $m=K^2$, and expansion (12), the first-copy assignment has cost at most $4m$. If $(U_v)_{v\in\mathcal V}$ are arbitrary base left subsets satisfying $\operatorname{dist}(u,v)<1$ for $u\in U_v$, and $U'=\bigcup_v U_v$, then
--   $$\sum_v\rho(U_v\times\mathbb Z_d)+d|\mathcal U\setminus U'|\ge d\tau(\mathcal U).$$
--   In particular, every whole-orbit assignment costs at least $d\tau(\mathcal U)$.
--
--   All three conclusions are included. The sets $U_v$ need not be disjoint, and the facilities are the base right vertices.
--
--   Differences from the source:
--   - encoding: two disjoint sides of size m and matching colours in ℤ_d → each side is indexed by Fin m, with its side distinguished in a sum, and cyclic colours by Fin d; reason: these are finite coordinate choices; every coloured edge, including repeated endpoints, is retained
--   - encoding: integer witness cost Φ and nonnegative rank ρ → Φ and the capped minimum are calculated in ℤ, with nonnegativity obtained from local expansion; reason: integer subtraction retains negative intermediate values and changes no value under the source assumptions
--   - encoding: nonnegative allocation costs, possibly +∞ → ENNReal costs and an infimum over feasible assignments; reason: there are finitely many assignments, so each nonempty feasible family attains its minimum; the empty feasible family has value +∞
--   - generalization: the base graph of Lemma 19 for sufficiently large d, including its large-cover property → any matching-decomposed graph with m=(d^(d+3))², d≥4 and expansion (12); reason: the proofs use expansion and the displayed cap, not the large-cover bound; they work for every d≥4, so include all sufficiently large source instances
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 25(i)–(ii), p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SparseRank

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 25(i)–(ii) and its whole-orbit consequence, p.24. -/

theorem first_copy_whole_orbit (d : ℕ) (hd : 4 ≤ d)
    (M : MatchingGraph d (graphSize d)) (hexp : BaseExpansion M (graphCap d)) :
    allocationCost (liftedData M) (sparseRankReal M (graphCap d)) (firstCopyAssignment M) ≤
      ((4 * graphSize d : ℕ) : ℝ≥0∞) ∧
    (∀ U : Fin (graphSize d) → Finset (Fin (graphSize d)),
      (∀ v, ∀ u ∈ U v, baseDistance M (Sum.inl u) (Sum.inr v) < 1) →
      ((d : ℤ) * coverNumber M univ) ≤
        (∑ v, sparseRank M (graphCap d) (fibers (U v))) +
        (d : ℤ) * (univ \ univ.biUnion U).card) ∧
    (∀ σ : (Fin (graphSize d) × Fin d) → Fin (graphSize d), FiberConstant σ →
      ((d * coverNumber M univ : ℕ) : ℝ≥0∞) ≤
        allocationCost (liftedData M) (sparseRankReal M (graphCap d)) σ) := by sorry

end SFLOracleLowerBound.Hardness
