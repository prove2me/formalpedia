-- Prove2me | Theorems.Thm_RepellingPairs_claim_9_flow_dominance
-- name    : RepellingPairs.claim_9_flow_dominance
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:13.396356+00:00
-- url     : https://prove2.me/theorems/356b2f41-daa8-4358-924b-9606ae7b5104
-- title:
--   Claim 9 — $C\succeq C'$ (corrected: no unit of $F$ on a trivial pair)
-- statement:
--   Let $(G,T)$ be an OS instance, $D$ a Kalmanson metric and $P$ a $D$-good shortest path structure (the standing assumption of §3), and let $F,F'$ be integral flows satisfying Property 2, Property 4 and Property 5, with no unit of $F$ on a trivial pair. Let $C$ and $C'$ be their configurations. Then $C\succeq C'$: for every pair of bars,
--
--   $$
--   \mathrm{dist}_{C'}(\bar i,\bar j)\le\mathrm{dist}_C(\bar i,\bar j).
--   $$
--
--   This turns the edge-by-edge comparison of Property 2 into a comparison of boundary cuts.
--
--   Differences from the source:
--   - correction: flows satisfying Properties 1, 2, 4 and 5 → in addition, no unit of F is on a trivial pair (t, t); reason: a trivial pair makes the claim false: on the path a — b — c with terminals a, b, c, D(a,b) = D(b,c) = 1, D(a,c) = 2 (realized by unit lengths, so the structure is D-good), take F = {(b,b), (a,c)} and F′ = {P a b, P b c}. Properties 2 and 4 hold and Property 5 is vacuous, but the cut around b is crossed by 2 chords of C′ and 0 of C. The hypothesis is met in the proof, since F₁ of Step 1 has no trivial pair
--   - encoding: a chord per unit of flow, n = number of terminals → Multiset (Sym2 (Fin k)), with a loop for a trivial path of F′; reason: F′ may contain trivial paths; two units may share a pair
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
--   - reading: Property 2: the amount of F through each edge is greater than the amount of F′ → load F′ ≤ load F on every edge; reason: the property as corrected on the Farkas alternative item, where the strict form is false (pendant-edge counterexample); the proof of Claim 9 (p.11) uses it as an edge-by-edge comparison
--   - reading: Property 4: the amount of flow sent from (received by, resp.) t is the same in F and F′ → the number of unit ends at t is the same, a trivial path counting twice; reason: the words come from the directed setting of [CT25]; for an undirected metric only the unit ends are meaningful (as on the normalization item)
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Claim 9, p.10

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

/-- **Claim 9.** In an OS instance with a Kalmanson metric `D` and a `D`-good structure `P` (the standing assumption
of §3, pp.7 and 9), for integral flows `F`, `F′` with Properties 2, 4 and 5 and no unit of `F` on a trivial pair, their
configurations satisfy `C ⪰ C′`. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026),
Claim 9, p.10.

**Formalization Note.** The printed proof never quotes Property 4, but the claim is false without it. The hypothesis
that `F` has no trivial pair is a correction: on the path `a — b — c` with `D(a,b) = D(b,c) = 1`, `D(a,c) = 2` (a
`D`-good structure), `F = {(b,b), (a,c)}` and `F′ = {P a b, P b c}` satisfy Properties 2, 4, 5 but not `C ⪰ C′`. -/
theorem claim_9_flow_dominance {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F) (hF : NoTrivialPair F) :
    Config.Dominates (DesignatedFlow.chords F) (PathFlow.chords F') := by sorry

end RepellingPairs
