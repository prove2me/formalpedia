-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_Supplement_lemma_1_parts_3_4
-- name    : SpatialDemandEq.Optimal.Supplement.lemma_1_parts_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:38:33.67263+00:00
-- url     : https://prove2.me/theorems/9e80b0aa-16b1-4382-afa1-e0a117c15e71
-- title:
--   Lemma 1 parts 3–4, p. 8 — ∂A_k/∂w_k ≤ 0, ∂A_k/∂w_j ≥ 0 for j ≠ k, and Σ_j ∂A_k/∂w_j = 0
-- statement:
--   Work in the spatial service model (region $\mathcal S$, demand $\nu$, distances $d_k$, constants $c,\lambda > 0$, under the standing assumptions). For a weight vector $w \in \mathbb R^K$ and a facility $k$, let $A_k(w) = \nu(\mathcal A_k(w))$ be the area of the weighted Voronoi cell
--   $$\mathcal A_k(w) = \{x \in \mathcal S : d_k(x) + w_k \le d_j(x) + w_j \ \text{ for all } j \ne k\}.$$
--   Suppose the map $w \mapsto A_k(w)$ is differentiable at $w$. Then
--
--   1. (part 3) $\dfrac{\partial A_k}{\partial w_k} \le 0$ and $\dfrac{\partial A_k}{\partial w_j} \ge 0$ for every $j \ne k$;
--   2. (part 4) $$\sum_j \frac{\partial A_k}{\partial w_j} = 0 .$$
--
--   Raising one's own weight makes a region less attractive, raising another's makes it more attractive, and adding a constant to all weights leaves the cells unchanged. These sign and row-sum facts are what make $I - D$ an M-matrix in Lemma 4.
--
--   **Formalization Note** $\partial A_k/\partial w_j$ is the Fréchet derivative of $w \mapsto A_k(w)$ at $w$ applied to the $j$-th unit vector.
--
--   Differences from the source:
--   - reading: the partial derivatives ∂A_k/∂w_j at w, presupposed to exist → the hypothesis that w ↦ A_k(w) is (Fréchet) differentiable at w, and ∂A_k/∂w_j = its derivative applied to e_j; reason: the paper writes the derivatives without stating a regularity condition; part 4 is the derivative along (1,…,1), which equals the sum of the partials for a differentiable map
--   - encoding: the standing assumptions of §3.1 → the published `Standing` of the base mission; reason: inherited base conventions, disclosed on the published definition
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 8, Lemma 1 parts 3–4

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open MeasureTheory SpatialDemandEq.Optimal

namespace SpatialDemandEq.Optimal.Supplement

theorem lemma_1_parts_3_4 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n))
    (dst : E n → E n → ℝ) (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam)
    (w : Fin K → ℝ) (k : Fin K)
    (hdiff : DifferentiableAt ℝ (fun w' : Fin K → ℝ => area ν (cell S (distFn dst xs) w' k)) w) :
    partialArea ν S (distFn dst xs) w k k ≤ 0 ∧
      (∀ j, j ≠ k → 0 ≤ partialArea ν S (distFn dst xs) w k j) ∧
      ∑ j, partialArea ν S (distFn dst xs) w k j = 0 := by sorry

end SpatialDemandEq.Optimal.Supplement
