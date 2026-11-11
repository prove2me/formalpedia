-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_split_point
-- name    : PlanarMetricElections.Peer.split_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:54.157955+00:00
-- url     : https://prove2.me/theorems/3a64ee18-fa65-444c-bd33-86fee3fbd003
-- title:
--   Lemma A.1 — directional split point
-- statement:
--   Let $V$ be a nonempty finite planar voter set, let $\varnothing\ne X\subseteq V$, and let $a,b\ge0$ with $a+b\le\mu_V(X)$. There is $z\in X$ for which
--
--   $$\mu_V(X\cap\{v:v_1>z_1\})\le\mu_V(X)-a,\qquad\mu_V(X\cap\{v:v_2<z_2\})\le\mu_V(X)-b.$$
--
--   This is the southeast directional split-point statement, with arbitrary admissible $a,b$, not only the balanced choice. No general-position or quartile-grid condition is imposed.
--
--   Differences from the source: none.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma A.1, p. 13 (PDF p. 14)

import Definitions.Def_PlanarMetricElections_Peer_Mass

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem split_point (V X : Finset Plane)
    (hXV : X ⊆ V) (hX : X.Nonempty) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ mass V (↑X : Set Plane)) :
    ∃ z ∈ X,
      mass V ((↑X : Set Plane) ∩ {v | z.1 < v.1}) ≤ mass V (↑X : Set Plane) - a ∧
      mass V ((↑X : Set Plane) ∩ {v | v.2 < z.2}) ≤ mass V (↑X : Set Plane) - b := by sorry

end PlanarMetricElections.Peer
