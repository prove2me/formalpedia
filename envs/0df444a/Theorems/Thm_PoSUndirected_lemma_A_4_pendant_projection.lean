-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_4_pendant_projection
-- name    : PoSUndirected.lemma_A_4_pendant_projection
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:32.346286+00:00
-- url     : https://prove2.me/theorems/cac7f2ed-a79d-4e60-a240-566fe849bbda
-- title:
--   Lemma A.4 — pendant projection: projected owner and portal routes are simple with pairwise acyclic unions
-- statement:
--   Consider the host of finite depth $d$ at $\eta(t)$, $0\le t<1$ rational, a weak equilibrium $A$, and a gadget of a block $b$ whose six chord owners are confined, whose floor owners are confined, and for which the smaller-height conclusions hold. The **projected core** has vertices $0,\dots,11$, the floors $r$–$(r+1)$ and the chords $x=08$, $y=17$, $z=2\,11$, $u=36$, $v=4\,10$, $w=59$. The **projected route** of a player consists of the floors whose segment region her path meets and the chords it contains; the pendants $Y$, $Z$ are contracted, so their regions have no image. Then:
--
--   1. the projected route of each of the six chord owners is a simple path of the core between the projected endpoints of her chord;
--   2. the projected route of each external user of the gadget region is a simple path of the core between the portals $0$ and $11$;
--   3. the projected routes of any two of these regional players have acyclic union.
--
--   This reduces a gadget to six owner routes and one portal route on a graph with twelve vertices, the setting of the finite case analysis of the local comparison. It is an equilibrium argument, using $y-L_y\ge4L_y$ and $z-L_z\ge4L_z$: contracting a pendant does not preserve arbitrary acyclic pairs of physical routes.
--
--   **Formalization Note** The projection is defined on every edge set. That a route crosses each segment whole is part of the conclusion, not a condition on the route.
--
--   Differences from the source:
--   - encoding: "contracting Y and Z gives simple projected owner and portal routes" → the core edge set of a route is the set of floors whose segment region it meets and the chords it contains; it is a simple path of the core between the projected endpoints of the chord (owners) or between $0$ and $11$ (external users); reason: this is the first projection of p.15 followed by the contraction; a route that met a segment without crossing it would fail the conclusion, so nothing is assumed about crossings
--   - encoding: pairwise unions of the projected owner and portal routes → any two of the six chord owners and the external users of the gadget region; reason: these are the regional players, §3, p.5 (PDF p.7)
--   - reading: the setting of the lemma, in the paragraph before it (p.15): "a gadget whose chord owners are confined. Floor confinement and the smaller-height conclusions are available" → hypotheses on the chord owners and floor owners of this gadget and the smaller-height conclusions of its block; reason: the printed sentence of the lemma states only equation (2); confinement is assumed only for the gadget under consideration, as in Lemma A.5
--   - encoding: "Under equation (2)" → the parameters are $\eta(t)$ with $t$ rational and $0\le t<1$; reason: §A.5, p.18 (PDF p.20): "Throughout the construction use η(t)"; equation (2) holds there and is a milestone of this mission
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.4 (Pendant projection), p.15 (PDF p.17). Fix the
construction at `η(t)`, `0 ≤ t < 1` rational (where equation (2) holds), of finite depth `d`, a weak
equilibrium `A`, and a gadget `g` of block `b` whose chord owners are confined, with floor
confinement for its floor units and the smaller-height conclusions available. Then, on the core
with `Y`, `Z` contracted:

1. the projected route of each of the six chord owners is a simple path between the projected
   endpoints of her chord;
2. the projected route of each external user of the gadget region is a simple path between the
   portals `0` and `11`;
3. the projected routes of any two of these regional players have acyclic union.

**Formalization Note.** The setting is the paragraph before the lemma on p.15. The projection
`projRoute` is defined on every edge set; that an actual route crosses each segment whole is part of
the conclusion. Equation (2) is discharged by fixing the parameters to `η(t)`, `0 ≤ t < 1`. The
equilibrium hypothesis is essential: the paper's proof "does not claim that contracting a pendant
preserves all arbitrary proper pairs". -/
theorem lemma_A_4_pendant_projection (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ)
    (A : HEdge d → Finset (HEdge d)) (hA : IsPureNash (hostGame (etaAt t) d) A) (b : HBlock d)
    (g : Fin 7) (hchord : ∀ κ, A (HEdge.chord b.1 b.2 g κ) ⊆ gadgetRegion b g)
    (hfloor : ∀ σ u, A (HEdge.floor b.1 b.2 g σ u) ⊆ unitRegion b.1 b.2 g σ u)
    (hsmall : SmallerHeightConcl (etaAt t) A b) :
    (∀ κ : Fin 6, IsSimplePathEdges coreEnds (coreChordEnds κ).1 (coreChordEnds κ).2
      (projRoute b g (A (HEdge.chord b.1 b.2 g κ)))) ∧
    (∀ i ∈ extUsers A (gadgetRegion b g),
      IsSimplePathEdges coreEnds 0 11 (projRoute b g (A i))) ∧
    (∀ i ∈ regionalPlayers A b g, ∀ j ∈ regionalPlayers A b g,
      IsAcyclicEdges coreEnds (projRoute b g (A i) ∪ projRoute b g (A j))) := by sorry

end PoSUndirected
