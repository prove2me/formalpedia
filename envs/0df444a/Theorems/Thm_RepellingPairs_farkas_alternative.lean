-- Prove2me | Theorems.Thm_RepellingPairs_farkas_alternative
-- name    : RepellingPairs.farkas_alternative
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:06:18.858975+00:00
-- url     : https://prove2.me/theorems/a0b31024-7dc4-4640-af8d-c743630d4abf
-- title:
--   §3, pp.7–8 — Farkas alternative (corrected: load F′ ≤ load F)
-- statement:
--   Let $(G,T)$ be an OS instance, $D$ a Kalmanson metric and $P$ a shortest path structure. Then there are nonnegative edge lengths under which every $P_{t,t'}$ is a shortest path of length $D(t,t')$ if and only if there is **no** pair of nonnegative real flows, $F$ on the designated paths and $F'$ on arbitrary paths, such that
--
--   1. for each edge $e$, the load of $F'$ on $e$ is at most the load of $F$ on $e$;
--   2. $\sum_{t,t'}F_{t,t'}D(t,t')<\sum_{t,t'}F'_{t,t'}D(t,t')$.
--
--   This is the reduction of the backward direction of Theorem 1 to the nonexistence of certain flows.
--
--   Differences from the source:
--   - correction: Property 2: the flow of F through each edge is greater than the flow of F′ → the load of F′ is at most the load of F (≤); reason: strict inequality is false: take the path a — b — c with a pendant edge b — y, terminals a, b, c on the boundary, D(a,b) = D(b,c) = 1, D(a,c) = 3/2 and P a c through b. The LP is infeasible, and the pendant edge carries 0 of F, so no pair of flows has the strict inequality on every edge
--   - generalization: in the setting where the paths of every repelling pair are disjoint (p.7) → no goodness hypothesis; reason: Farkas' lemma does not use it, and the statement specializes to the source's setting
--   - encoding: flows F, F′ in G → F on ordered pairs; F′ a finitely supported weight on terminal paths; reason: the sum over t, t′ ∈ T is over ordered pairs and P i j, P j i use the same edges; a finite graph has finitely many paths
--   - encoding: Pt,t′ is shortest among t-t′ paths → Q ranges over paths, that is, walks with no repeated vertex; reason: the LP of §3, p.7 uses simple paths; for nonnegative lengths this equals the minimum over all walks
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3, pp.7–8

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

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- **§3, Farkas alternative (corrected: `load F′ ≤ load F`).** Edge lengths as in Theorem 1 exist if and only
if there is no pair of nonnegative real flows, `F` on the designated paths and `F′` on arbitrary paths,
with `load F′ ≤ load F` on every edge and `∑ F D < ∑ F′ D`. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version
of October 23, 2026), §3, pp.7–8.

**Formalization Note.** The page prints Property 2 as "greater than"; Farkas' lemma gives only `≥`. `F′` is
finitely supported, a finite multigraph having finitely many paths. -/
theorem farkas_alternative {V : Type u} {E : Type v} {k : ℕ} [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) :
    (∃ ℓ : E → ℝ, (∀ e, 0 ≤ ℓ e) ∧ ∀ i j,
        (P.path i j).1.len ℓ = D i j ∧
        ∀ Q : G.graph.Path (G.term i) (G.term j), (P.path i j).1.len ℓ ≤ Q.1.len ℓ) ↔
    ¬ ∃ (F : Fin k → Fin k → ℝ) (F' : TerminalPath G →₀ ℝ),
        (∀ i j, 0 ≤ F i j) ∧ (∀ q, 0 ≤ F' q) ∧
        (∀ e, realPathLoad F' e ≤ realLoad P F e) ∧
        realCost D F < realPathCost D F' := by sorry

end RepellingPairs
