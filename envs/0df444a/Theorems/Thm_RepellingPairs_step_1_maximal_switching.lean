-- Prove2me | Theorems.Thm_RepellingPairs_step_1_maximal_switching
-- name    : RepellingPairs.step_1_maximal_switching
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:07:01.613694+00:00
-- url     : https://prove2.me/theorems/60a3fefd-da96-4993-93d1-be9b974e7aff
-- title:
--   §3.2, Step 1 — Property 5 can be added by maximal switching
-- statement:
--   Let $(G,T)$ be an OS instance, $D$ a Kalmanson metric and $P$ a $D$-good shortest path structure. If integral flows $F,F'$ satisfy Properties 2, 3 and 4, then there is an integral $F_1$, with the same $F'$, satisfying Properties 2, 3 and 4 and also
--
--   **Property 5**: for terminals $s,s',t',t$ on the boundary in this order with $(F_1)_{s,s'},(F_1)_{t,t'}>0$, the designated paths $P_{s,s'}$ and $P_{t,t'}$ are disjoint.
--
--   Moreover, if $F$ has no unit on a trivial pair, neither does $F_1$.
--
--   This step removes pairs of units of $F$ whose chords do not cross but whose paths meet.
--
--   Differences from the source:
--   - generalization: there exist flows F, F′ satisfying Properties 1–5 → F₁ keeps the given F′, and also keeps "no trivial pair" when F has it; reason: a stronger conclusion (the switching changes only F, as on p.10, and preserves the clause); dropping it recovers the source
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
--   - reading: Property 2: the amount of F through each edge is greater than the amount of F′ → load F′ ≤ load F on every edge; reason: the property as corrected on the Farkas alternative item, where the strict form is false (pendant-edge counterexample); the proof of Claim 9 (p.11) uses it as an edge-by-edge comparison
--   - reading: Property 4: the amount of flow sent from (received by, resp.) t is the same in F and F′ → the number of unit ends at t is the same, a trivial path counting twice; reason: the words come from the directed setting of [CT25]; for an undirected metric only the unit ends are meaningful (as on the normalization item)
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3.2, pp.9–10

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

/-- **§3.2, Step 1.** If the structure is `D`-good and integral flows `F`, `F′` satisfy Properties 2, 3 and 4, then some
integral `F₁`, with the same `F′`, satisfies Properties 2, 3, 4 and 5; and `F₁` has no unit on a trivial pair if
`F` has none. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3.2,
pp.9–10. -/
theorem step_1_maximal_switching {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D)
    (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h3 : Property3 D F F') (h4 : Property4 F F') :
    ∃ F₁ : DesignatedFlow k,
      Property2 P F₁ F' ∧ Property3 D F₁ F' ∧ Property4 F₁ F' ∧ Property5 P F₁ ∧
        (NoTrivialPair F → NoTrivialPair F₁) := by sorry

end RepellingPairs
