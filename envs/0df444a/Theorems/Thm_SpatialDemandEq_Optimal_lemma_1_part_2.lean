-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_lemma_1_part_2
-- name    : SpatialDemandEq.Optimal.lemma_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:04.064613+00:00
-- url     : https://prove2.me/theorems/30c72a67-5eaf-4ea3-868d-fc6440f41d2e
-- title:
--   Lemma 1 part 2, p. 8 — if w_k − w̃_k ≥ w_j − w̃_j for all j then A_k(w) ≤ A_k(w̃)
-- statement:
--   Let $\mathcal S \subseteq \mathbb R^n$, let $\nu$ be a measure, let $d_1,\dots,d_K : \mathbb R^n \to \mathbb R$, and for weights $w \in \mathbb R^K$ let
--   $$\mathcal A_k(w) = \{x \in \mathcal S : d_k(x) + w_k \le d_j(x) + w_j \text{ for all } j \ne k\}$$
--   be the additively weighted Voronoi cells (2). If $w, \tilde w \in \mathbb R^K$ satisfy $w_k - \tilde w_k \ge w_j - \tilde w_j$ for all $j$, then
--   $$\nu(\mathcal A_k(w)) \le \nu(\mathcal A_k(\tilde w)),$$
--   i.e. $A_k(w) \le A_k(\tilde w)$.
--
--   Raising the weight of facility $k$ relative to every other facility can only shrink its region. This monotonicity is the comparison step in the uniqueness proof of the equilibrium weights (Theorem 2).
--
--   **Formalization Note** The statement is phrased with the measure $\nu$ of the cells, which equals the area for the probability measure of the model; it holds for every measure, so no hypothesis on $\nu$, $\mathcal S$ or the $d_k$ is needed.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 8, Lemma 1 part 2; cells (2), p. 8

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem lemma_1_part_2 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (d : Fin K → E n → ℝ)
    (w w' : Fin K → ℝ) (k : Fin K) (h : ∀ j, w j - w' j ≤ w k - w' k) :
    ν (cell S d w k) ≤ ν (cell S d w' k) := by sorry

end SpatialDemandEq.Optimal
