-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_Supplement_euclidean_four_condorcet
-- name    : PlanarMetricElections.Peer.Supplement.euclidean_four_condorcet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:44:31.489208+00:00
-- url     : https://prove2.me/theorems/8fdf3c17-3546-4f0c-b77a-552595ed0391
-- title:
--   Theorem 5.5 — four candidates suffice under $\ell_2$: $\mathrm{RR}_{\ell_2}(4)\le 1/2$ on the plane
-- statement:
--   Let $V\subseteq\mathbb R^2$ be a nonempty finite set of voters and $C\subseteq\mathbb R^2$ a nonempty finite set of candidates (they may overlap), with distances measured by the Euclidean distance $d_2$, and assume no voter is equidistant from two distinct candidates. Then there is a nonempty coalition $S\subseteq C$ with $|S|\le4$ such that every candidate $c\in C$ satisfies
--
--   $$\frac{|\{v\in V:\ d_2(v,c)<d_2(v,s)\ \text{for all } s\in S\}|}{|V|}\le\frac12 .$$
--
--   That is, $S$ is a Condorcet-winning set of size at most four: no candidate is strictly preferred to every member of $S$ by a strict majority of voters. Equivalently, $\mathrm{RR}_{\ell_2}(4)\le1/2$ on the plane.
--
--   This improves the general bound of five candidates for metric elections in the Euclidean plane. Singleton electorates and candidate sets, collinear points and repeated coordinates are all included.
--
--   Differences from the source:
--   - encoding: the factor inequality RRℓ2(4) ≤ 1/2 → for every planar Euclidean election, existence of a coalition S ⊆ C with 1 ≤ |S| ≤ 4 and every c ∈ C capturing at most half of V; reason: the source states both forms ("that is"); for fixed (V,C) the coalitions form a finite nonempty family and payoffs a finite set, so the extrema are attained and the forms are equivalent
--   - encoding: Condorcet condition for c ∈ C ∖ S → bound for every c ∈ C; reason: a candidate in S captures no voter, so the two are equivalent
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Theorem 5.5, p. 11 (PDF p. 12)

import Definitions.Def_PlanarMetricElections_Peer_Capture
import Definitions.Def_PlanarMetricElections_Peer_Supplement_EuclideanPlane

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer.Supplement

theorem euclidean_four_condorcet (V C : Finset Plane) (hV : V.Nonempty) (hC : C.Nonempty)
    (hties : NoEquidistantVoter dTwo V C) :
    ∃ S : Finset Plane, FeasibleCoalition C S 4 ∧
      ∀ c ∈ C, capturePayoff dTwo V S c ≤ 1 / 2 := by sorry

end PlanarMetricElections.Peer.Supplement
