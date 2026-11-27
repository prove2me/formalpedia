-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_Supplement_lemma_6_3_total_demand_bound
-- name    : PLCMarkets.ExactCover.Supplement.lemma_6_3_total_demand_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:20:32.590707+00:00
-- url     : https://prove2.me/theorems/94ef4c3c-f334-4989-85f3-c62c0c9684a9
-- title:
--   LEMMA 6.3 — at every vertex of the fixed-point cell, and at $x^*$, total demand is at most $1+4ng\delta$
-- statement:
--   Let $M$ be an Arrow–Debreu market with $n$ agents and $g$ goods in which the total supply of every good is $1$, with piecewise-linear concave utilities trimmed at $1.1$ units, and let $F:S\times D\rightrightarrows S\times D$ be the correspondence of §6 on the product of the price simplex $S$ and the demand box $D=[0,1.1]^{ng}$. Let $m\in\mathbb N$ and $\delta=2^{-10m}$. Let $C$ be a cell whose vertices $(p_v,x_v)\in S\times D$ are pairwise equal or $\delta$ apart in each coordinate, let $G(p_v,x_v)\in F(p_v,x_v)$ be the selected values at the vertices, and let $(p^*,x^*)$ be a fixed point of the linear interpolation of $G$ on $C$: it is the same convex combination of the vertices and of their $G$-values.
--
--   Then for every vertex $(p,x)$ of $C$ and every good $j$, the total demand for good $j$ in $x$ satisfies
--   $$x_j=\sum_{i}x_{ij}\le1+4ng\delta,$$
--   and the same bound holds for the total demands of $x^*$.
--
--   The lemma shows that the demands at the approximate fixed point exceed the supplies by at most $4ng\delta$; together with Lemma 6.4 it lets the proof of Theorem 6.1 round $(p^*,x^*)$ to an exact equilibrium with a linear program.
--
--   **Formalization Note** The cell, the correspondence and the fixed point are the objects of the `FixedPointCell` item. The bound is proved for both the vertices (first conjunct) and $x^*$ (second conjunct).
--
--   Differences from the source:
--   - generalization: δ = 1/2^{10m} with m the specific LP bit bound of p. 10:12 → δ = 1/2^{10m} for an arbitrary natural number m; reason: the bound is claimed for every m, so it holds for the paper's m
--   - generalization: C the cell of a regular simplicization of S × D of resolution δ that contains the fixed point of G → any finite family of vertices in S × D whose coordinates are pairwise equal or differ by δ, with a fixed point given by barycentric weights; reason: every cell of the paper's simplicization has this property (p. 10:12), and the selection G and the fixed point are recorded at its vertices
--   - generalization: the market satisfies (C') and non-flat slopes are integers (standing assumptions of §6, pp. 10:11–10:12) → neither is assumed; reason: the lemma's statement and argument do not involve them, and markets satisfying them are included
--   - encoding: total initial supply of each good is 1, without loss of generality (§6, p. 10:10) → hypothesis Σ_i w_ij = 1 for every good j; reason: the §6 normalization under which S × D and the bound are stated
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:12, LEMMA 6.3 (setting: §6, pp. 10:10–10:12)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_Supplement_FixedPointCell

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

theorem lemma_6_3_total_demand_bound {n g : ℕ} (M : ADMarket (Fin n) (Fin g))
    (hsupply : ∀ j, M.supply j = 1) (m : ℕ) (C : FixedPointCell M (mesh m)) :
    (∀ a j, totalDemand (C.vertex a).2 j ≤ 1 + 4 * n * g * mesh m) ∧
      ∀ j, totalDemand C.xStar j ≤ 1 + 4 * n * g * mesh m := by sorry

end PLCMarkets.ExactCover.Supplement
