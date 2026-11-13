-- Prove2me | Theorems.Thm_RepellingPairs_flow_normalization
-- name    : RepellingPairs.flow_normalization
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:07:08.414497+00:00
-- url     : https://prove2.me/theorems/283d42e5-fa04-4ca4-91f3-9a80b51b75ec
-- title:
--   §3, p.8 — flows can be made integral and aligned (Property 4)
-- statement:
--   Let $(G,T)$ be an OS instance, $D$ a Kalmanson metric and $P$ a $D$-good shortest path structure. If nonnegative real flows $F,F'$ satisfy Properties 2 and 3, then there are **integral** flows $F_1$ (units on designated paths) and $F_1'$ (units on paths) satisfying
--
--   1. Property 2: the load of $F_1'$ on each edge is at most the load of $F_1$;
--   2. Property 3: $\sum_{F_1}D<\sum_{F_1'}D$;
--   3. Property 4: at each terminal, $F_1$ and $F_1'$ have the same number of unit ends;
--
--   and no unit of $F_1$ is on a trivial pair $(t,t)$.
--
--   This places the flow problem in the form to which the chord arguments of §3 apply.
--
--   Differences from the source:
--   - reading: the total amount of flow sent from (received by, resp.) t → the number of unit ends at t, a trivial path counting twice; reason: the words come from the directed setting of [CT25]; for an undirected metric only the unit ends are meaningful
--   - reading: F′ may use any paths → F′ may contain trivial paths; reason: §2, p.6 represents the pair (t, t) by the trivial path at t; trivial units of F′ carry no load and no cost
--   - generalization: the conversion gives Property 4; integrality is assumed separately ("as Q is dense in R", p.8) → one statement gives integrality, Property 4 and no unit of F on a trivial pair; reason: a stronger conclusion than each printed step; dropping clauses recovers them
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
--   - reading: Property 2: the amount of F through each edge is greater than the amount of F′ → load F′ ≤ load F on every edge; reason: the property as corrected on the Farkas alternative item, where the strict form is false (pendant-edge counterexample); the proof of Claim 9 (p.11) uses it as an edge-by-edge comparison
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3, p.8

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_PathLength
import Definitions.Def_RepellingPairs_Repel
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_RealFlow
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_IntegralFlow

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- **§3, Property 4 and integrality.** If the structure is `D`-good, any nonnegative real flows `F`, `F′` with
Properties 2 and 3 can be converted to integral flows with Properties 2, 3 and 4, with no unit of `F` on a
trivial pair. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3, p.8.

**Formalization Note.** For an undirected metric "sent from / received by" is the number of unit ends at the
terminal. `F′` may use trivial paths, each counting two ends. -/
theorem flow_normalization {V : Type u} {E : Type v} {k : ℕ} [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D)
    (F : Fin k → Fin k → ℝ) (F' : TerminalPath G →₀ ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hF' : ∀ q, 0 ≤ F' q)
    (hload : ∀ e, realPathLoad F' e ≤ realLoad P F e)
    (hcost : realCost D F < realPathCost D F') :
    ∃ (F₁ : DesignatedFlow k) (F₁' : PathFlow G),
      Property2 P F₁ F₁' ∧ Property3 D F₁ F₁' ∧ Property4 F₁ F₁' ∧ NoTrivialPair F₁ := by sorry

end RepellingPairs
