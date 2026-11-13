-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_strong_peer_three
-- name    : PlanarMetricElections.Peer.strong_peer_three
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:42.174894+00:00
-- url     : https://prove2.me/theorems/118ab37f-1d7a-492f-992e-9d3e725f450f
-- title:
--   Theorem 5.7 — three voters suffice for both norms
-- statement:
--   Let $V\subset\mathbb R^2$ be any nonempty finite set of distinct voters, with equal weight per voter. For each of the distances $d_1$ and $d_\infty$ separately, there exists a nonempty coalition $S\subseteq V$ of at most three voters such that every challenger $c\in\mathbb R^2$ satisfies
--
--   $$\frac{|\{v\in V:\forall s\in S,\ d(v,c)<d(v,s)\}|}{|V|}\le\frac12.$$
--
--   Thus both strong-peer factors satisfy $\mathrm{PF}_{d_1}(3)\le1/2$ and $\mathrm{PF}_{d_\infty}(3)\le1/2$. The two norms may use different coalitions. Ties are not captured voters; challengers can be placed anywhere in the real plane. Singleton electorates, collinear voters, and repeated coordinate values are included. Restricting the challenger to $V$ gives the peer-selection Condorcet-winning-set consequence.
--
--   Differences from the source:
--   - encoding: the pair of worst-case factor inequalities PFℓ1(3) ≤ 1/2 and PFℓ∞(3) ≤ 1/2 → the conjunction of the corresponding coalition guarantees for every nonempty finite V; reason: for fixed V the feasible coalition family is finite and nonempty, and captured fractions range over a finite set, so the minima and maxima are attained; the statements are equivalent
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Theorem 5.7, p. 11 (PDF p. 12)

import Definitions.Def_PlanarMetricElections_Peer_Capture

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem strong_peer_three (V : Finset Plane) (hV : V.Nonempty) :
    StrongPeerGuarantee dOne V 3 (1 / 2) ∧
    StrongPeerGuarantee dInf V 3 (1 / 2) := by sorry

end PlanarMetricElections.Peer
