-- Prove2me | Theorems.Thm_RepellingPairs_cost_inequality
-- name    : RepellingPairs.cost_inequality
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:07:10.997571+00:00
-- url     : https://prove2.me/theorems/a220258e-f316-4ace-866e-ef3da7e0deb3
-- title:
--   §3.4, pp.13–14 — Property 3 fails
-- statement:
--   Let $(G,T)$ be an OS instance, $D$ a Kalmanson metric and $P$ a $D$-good shortest path structure (the standing assumption of §3). If integral flows $F,F'$ satisfy Properties 2, 4 and 5, then
--
--   $$
--   \sum_{F'}D\le\sum_{F}D,
--   $$
--
--   so Property 3 cannot hold.
--
--   Together with the earlier milestones this finishes the backward direction of Theorem 1.
--
--   Differences from the source:
--   - reading: "As D(·, ·) = distG(·, ·)" and the four-point inequality for distG (p.14) → the hypothesis that D is Kalmanson; reason: no realization exists in this direction yet; the text before the lemma names "the four-point condition of Okamura-Seymour metrics" (p.11)
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
--   - reading: Property 2: the amount of F through each edge is greater than the amount of F′ → load F′ ≤ load F on every edge; reason: the property as corrected on the Farkas alternative item, where the strict form is false (pendant-edge counterexample); the proof of Claim 9 (p.11) uses it as an edge-by-edge comparison
--   - reading: Property 4: the amount of flow sent from (received by, resp.) t is the same in F and F′ → the number of unit ends at t is the same, a trivial path counting twice; reason: the words come from the directed setting of [CT25]; for an undirected metric only the unit ends are meaningful (as on the normalization item)
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3.4, pp.13–14

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_IntegralFlow

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- **§3.4, completing the proof.** In an OS instance with a Kalmanson metric `D` and a `D`-good structure `P` (the
standing assumption of §3, pp.7 and 9), for integral flows `F`, `F′` with Properties 2, 4 and 5, Property 3 fails:
`∑ F′ D ≤ ∑ F D`. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3.4, pp.13–14.

**Formalization Note.** The page writes "As D(·, ·) = distG(·, ·)", which cannot be literal before edge lengths exist; the
four-point inequality used is the hypothesis that `D` is Kalmanson. Units of `F` on a trivial pair `(t, t)` are allowed, as on
the page: under `D`-goodness they change neither side (unlike in Claim 9). -/
theorem cost_inequality {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F) :
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F := by sorry

end RepellingPairs
