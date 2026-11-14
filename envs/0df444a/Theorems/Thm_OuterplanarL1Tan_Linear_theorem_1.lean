-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_theorem_1
-- name    : OuterplanarL1Tan.Linear.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:00.60607+00:00
-- url     : https://prove2.me/theorems/01397fb4-3365-401d-95d7-cd908fc74f92
-- title:
--   Theorem 1 — noncontracting ℓ₁ embeddings with distortion at most 192k
-- statement:
--   Let $k\ge0$ be an integer and $G$ a finite undirected graph with symmetric nonnegative real edge lengths and finite shortest-path distances $d_G$. Suppose a plane drawing of $G$ is exhausted by at most $k$ rounds of deleting its outer-face vertices. There exist a finite dimension $N$ and a single map $F:V(G)\to\ell_1^N$ such that for every pair $x,y\in V(G)$,
--
--   $$d_G(x,y)\le\|F(x)-F(y)\|_1\le192k\,d_G(x,y).$$
--
--   The constant $192$ is fixed uniformly over graph size, weights, drawing, endpoints and $k$. Theorem 1 is stated with $O(k)$ in the source; the complete proof in §3.3 gives an unscaled map with lower bound $d_G/32$ and upper bound $6kd_G$. Multiplying that map by $32$ yields precisely the displayed quantitative noncontracting conclusion.
--
--   This is the paper's headline theorem with its own proof's constant retained. Residual graphs may be disconnected and may distort ambient distances arbitrarily. Empty graphs, singleton graphs and coincident points from zero-length edges are included; $k=0$ permits exactly the empty graph.
--
--   **Formalization Note** Shortest-path distance reuses `PlanarL1`; the chosen drawing, outer face and peeling are geometric. Output finite vectors have the true ℓ₁ norm. Zero-padding realizes the same map in the infinite sequence space. The already Proved all-planar theorem is included as background with an unspecified constant, and is not assumed to give this $192k$ bound.
--
--   Differences from the source:
--   - encoding: edge-weighted k-outerplanar graph with a shortest-path metric → an arbitrary Fintype vertex carrier, symmetric real edge lengths on SimpleGraph, and an actual walk for each pair; reason: the paper's graphs are finite (§3.3 applies the finite-X Lemma 6 to V(H) and uses diam(G)); a disconnected graph has infinite distances, which no ℓ₁ map could satisfy in the lower bound, so reachability excludes only undefined cases; nonnegative loops may be removed and parallel edges replaced by a minimum-length drawn edge, preserving distances without increasing peeling depth
--   - generalization: shortest-path metrics → nonnegative real edge lengths allowing pseudometric coincidences; reason: every metric instance remains included; the distance-difference and localization arguments also apply to zero-length edges
--   - generalization: the asymptotic O(k) distortion of Theorem 1 → the explicit noncontracting bound 192k; reason: §3.3 proves d/32 and 6kd before scaling; multiplication by 32 gives 192k uniformly; the explicit constant implies the source’s O(k)
--   - generalization: an output in ℓ₁ → a finite dimension N and an output in PiLp 1 over Fin N; reason: the source proof gives finitely many coordinates; padding with zeros recovers summable real sequences without changing any norm; this implies the source’s ℓ₁ conclusion
--   - encoding: a graph admits a plane drawing exhausted in at most k rounds → existence of a continuous-arc drawing whose recursively defined geometric residual after k rounds is empty; reason: this is the stated definition of k-outerplanarity and adds no hypothesis on residual connectedness or ambient isometry
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 1, 7, Theorem 1 and §3.3 expansion/separation bounds (PDF p. 2, 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern

namespace OuterplanarL1Tan.Linear

/-- Theorem 1, printed p.1 (PDF p.2), with the quantitative bound from §3.3,
printed p.7 (PDF p.8): the proof's map has bounds d/32 and 6kd.
Scaling by 32 gives simultaneous noncontraction and the explicit 192k bound.
There are no assumptions on connectivity or metric convexity of residuals. -/
theorem theorem_1 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (k : ℕ) (outerplanar : IsKOuterplanar W.graph k) :
    ∃ N : ℕ, ∃ F : V → L1Vector N, ∀ x y : V,
      W.distance x y ≤ ‖F x - F y‖ ∧
      ‖F x - F y‖ ≤ (192 : ℝ) * (k : ℝ) * W.distance x y := by sorry

end OuterplanarL1Tan.Linear
