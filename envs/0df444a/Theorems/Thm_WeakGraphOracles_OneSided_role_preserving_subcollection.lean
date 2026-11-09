-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_role_preserving_subcollection
-- name    : WeakGraphOracles.OneSided.role_preserving_subcollection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:17.33725+00:00
-- url     : https://prove2.me/theorems/48090d19-e8b4-4cdf-92b0-3673f97cdac1
-- title:
--   Lemma 4.2 — role-preserving subcollection
-- statement:
--   Let $H$ be a connected labeled graph with $k\ge1$ edges and $r$ vertices. Let $\epsilon>0$, let $G$ be $\epsilon$-far from $H$-freeness in the edge normalization, and let $C$ be a supplied edge-disjoint collection with $|C|\ge\epsilon|E(G)|/k$. There exists a subcollection $C'\subseteq C$, with its original copy labelings, that is edge disjoint and role preserving, and
--
--   $$|C'|\ge\frac{\epsilon|E(G)|}{2k\,r^r}.$$
--
--   Role preservation means a single map $\rho:V(G)\to V(H)$ sends the image of each vertex $a$ of each supplied copy back to $a$. Copies can share vertices. The printed factor $2$ is retained even though §7.1 proves a stronger bound. This is the shared labeling structure used by tree discovery.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: minimum number of actual edge deletions, with strict farness → ENNReal infimum of cardinalities of feasible deletion sets; comparison with ENNReal.ofReal of epsilon times the edge or vertex count; reason: the feasible family is finite and nonempty for the stated patterns, so the infimum is its attained integer minimum; empty feasible families have value infinity, never a fabricated zero
--   - encoding: H has k edges and r vertices → k is computed as the edge cardinality and r as H.order; reason: avoids independent parameters while preserving all instances and the printed denominator
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 7 (PDF p. 8), Lemma 4.2 and Definition 5; proof p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Lemma 4.2; the printed denominator is 2*k*r^r, not the
stronger denominator proved in §7.1. Supplied copy labelings are retained. -/
theorem role_preserving_subcollection (H : Pattern) (hH : EligiblePattern H)
    {n : ℕ} (G : SimpleGraph (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hfar : EdgeFar {H} ε G) (C : Finset (Appearance H G))
    (hdis : EdgeDisjoint C)
    (hsize : ε * (edges G).card / (edges H.graph).card ≤ (C.card : ℝ)) :
    ∃ C' : Finset (Appearance H G), C' ⊆ C ∧ EdgeDisjoint C' ∧
      RolePreserving C' ∧
      ε * (edges G).card /
        (2 * (edges H.graph).card * (H.order : ℝ) ^ H.order) ≤ (C'.card : ℝ) := by sorry

end WeakGraphOracles.OneSided
