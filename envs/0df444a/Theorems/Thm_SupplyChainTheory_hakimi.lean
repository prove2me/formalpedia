-- Prove2me | Theorems.Thm_SupplyChainTheory_hakimi
-- name    : SupplyChainTheory.hakimi
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:42:07.7746+00:00
-- url     : https://prove2.me/theorems/c3fe9b2e-7991-403b-b185-269d7a5a1cc7
-- title:
--   Theorem 8.7 (Hakimi): the $p$-median problem on a network has an optimal solution consisting of nodes
-- statement:
--   **Theorem 8.7 (Hakimi 1965).** Consider a network with node set $I$ (the customers, with
--   weights $h_i \ge 0$), node-to-node shortest-path distances $d$, and edges of positive length,
--   so that the distance from node $i$ to a point at position $t$ along an edge $(u, w)$ of length
--   $\ell$ is $\min\{d(i, u) + t\ell,\ d(i, w) + (1-t)\ell\}$. For $1 \le p \le |I|$ there exists a set
--   $I^*_p \subseteq I$ of $p$ nodes such that, for any set $X$ of $p$ points on the network (nodes
--   or edges),
--
--   $$ \sum_{i \in I} h_i\, c(i, I^*_p) \;\le\; \sum_{i \in I} h_i\, c(i, X), $$
--
--   where $c(i, \cdot)$ is the distance to the nearest point of the set. The $p$-median problem may
--   therefore be treated as a discrete problem over node subsets. The reason is that, as a point
--   slides along an edge, its distance to every node is concave in the position, so the weighted
--   sum of distances of the customers it serves is concave and is minimized at an endpoint.
--
--   **Formalization Note** The set $X$ is a family of $p$ points, repetitions allowed, which only
--   strengthens the claim, and the node set produced has exactly $p$ elements. Two properties of the
--   book's network are hypotheses. First, $d$ is a shortest-path distance, so it satisfies the
--   triangle inequality. Second, each point lies on an edge whose length is at least the distance
--   between its endpoints, since the edge is itself a path. Together they make the endpoints of an
--   edge ($t = 0, 1$) coincide with its nodes ($\min\{d(i,u), d(i,w) + \ell\} = d(i,u)$), and the
--   concavity argument moves points to endpoints. Without them the statement is false: with two
--   nodes at distance $10$, unit weights, $p = 1$ and a point at the middle of an "edge" of length
--   $1$ between them, the point costs $1$ and either node costs $10$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 298, Sect. 8.3.2, Theorem 8.7 (Hakimi (1965))

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem hakimi {n p : ℕ} (d : Fin n → Fin n → ℝ) (hw : Fin n → ℝ) (hwn : ∀ i, 0 ≤ hw i)
    (hp : 1 ≤ p) (hpn : p ≤ n)
    (htri : ∀ i j k : Fin n, d i k ≤ d i j + d j k)
    (X : Fin p → NetPoint n)
    (hedge : ∀ k, d (X k).u (X k).w ≤ (X k).len ∧ d (X k).w (X k).u ≤ (X k).len) :
    ∃ S : Finset (Fin n), S.card = p ∧
      ∑ i, hw i * nearestNodeDist d i S ≤ ∑ i, hw i * nearestDist d i X := by sorry

end SupplyChainTheory
