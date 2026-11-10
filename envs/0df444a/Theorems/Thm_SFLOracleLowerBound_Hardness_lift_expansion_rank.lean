-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_lift_expansion_rank
-- name    : SFLOracleLowerBound.Hardness.lift_expansion_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:28:01.971196+00:00
-- url     : https://prove2.me/theorems/4590b732-c77b-437f-af2e-14529132f5eb
-- title:
--   Lemma 22 — Expansion and the rank of unions of fibers
-- statement:
--   For $d\ge4$, $K=d^{d+3}$, $m=K^2$, and any matching-decomposed base graph satisfying expansion (12), its cyclic lift satisfies local expansion up to $2K$. For every base left set $U$,
--   $$\rho(U\times\mathbb Z_d)\ge\min\{K,d\tau(U)\}.$$
--   The rank and cover number are the computed witness minimum and covering minimum. This relates whole-fiber rank to the cover number, including the cap.
--
--   Differences from the source:
--   - encoding: two disjoint sides of size m and matching colours in ℤ_d → each side is indexed by Fin m, with its side distinguished in a sum, and cyclic colours by Fin d; reason: these are finite coordinate choices; every coloured edge, including repeated endpoints, is retained
--   - encoding: integer witness cost Φ and nonnegative rank ρ → Φ and the capped minimum are calculated in ℤ, with nonnegativity obtained from local expansion; reason: integer subtraction retains negative intermediate values and changes no value under the source assumptions
--   - generalization: the base graph of Lemma 19 for sufficiently large d, including its large-cover property → any matching-decomposed graph with m=(d^(d+3))², d≥4 and expansion (12); reason: the proofs use expansion and the displayed cap, not the large-cover bound; they work for every d≥4, so include all sufficiently large source instances
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 22, p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SparseRank

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 22, p.22. The proof works for every d ≥ 4. -/

theorem lift_expansion_rank (d : ℕ) (hd : 4 ≤ d)
    (M : MatchingGraph d (graphSize d)) (hexp : BaseExpansion M (graphCap d)) :
    LiftExpansion M (graphCap d) ∧ ∀ U : Finset (Fin (graphSize d)),
      min (graphCap d : ℤ) ((d : ℤ) * coverNumber M U) ≤
        sparseRank M (graphCap d) (fibers U) := by sorry

end SFLOracleLowerBound.Hardness
