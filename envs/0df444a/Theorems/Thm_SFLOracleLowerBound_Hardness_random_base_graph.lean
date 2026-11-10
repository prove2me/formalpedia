-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_random_base_graph
-- name    : SFLOracleLowerBound.Hardness.random_base_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:26:59.38318+00:00
-- url     : https://prove2.me/theorems/83390d76-df7f-43f5-b8f8-b47274dfbbd4
-- title:
--   Lemma 19 — Random base graph
-- statement:
--   There is a threshold $d_0\ge4$ such that for every integer $d\ge d_0$, with $K=d^{d+3}$ and $m=K^2$, there exists a $d$-regular bipartite multigraph on $m$ vertices per side, decomposed into perfect matchings indexed by $\mathbb Z_d$, for which
--   $$\tau(\mathcal U)\ge\frac{m\log d}{2d},\qquad |N_G(V)|\ge(d-2)|V|\quad(|V|\le2K).$$
--   This is the source graph-existence result, retaining its large-cover and local-expansion conclusions. The threshold is uniform over all larger $d$.
--
--   Differences from the source:
--   - encoding: two disjoint sides of size m and matching colours in ℤ_d → each side is indexed by Fin m, with its side distinguished in a sum, and cyclic colours by Fin d; reason: these are finite coordinate choices; every coloured edge, including repeated endpoints, is retained
--   - encoding: d is sufficiently large → there exists a threshold d₀≥4 and every d≥d₀ is allowed; reason: this makes the section standing convention explicit without choosing an unverified numerical threshold
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 19, p.18; standing parameters (11), p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_MatchingGraph

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 19, p.18, with the standing sufficiently-large-d convention of p.17. -/

theorem random_base_graph : ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
    ∃ M : MatchingGraph d (graphSize d),
      ((graphSize d : ℕ) : ℝ) * Real.log d / (2*d) ≤ coverNumber M univ ∧
      BaseExpansion M (graphCap d) := by sorry

end SFLOracleLowerBound.Hardness
