-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_theorem_4
-- name    : SpatialDemandEq.Optimal.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:10.343267+00:00
-- url     : https://prove2.me/theorems/96326196-5f07-48ad-8e8d-34733b7f3be1
-- title:
--   Theorem 4, p. 14 — any local optimum of (9)–(12) is a weighted Voronoi diagram with weights ∂G(Ā)/∂A_k
-- statement:
--   Work in the setting of §4.1: $\mathcal S \subseteq \mathbb R^n$ is closed and convex, $\nu$ is a probability measure on $\mathcal S$ absolutely continuous with respect to Lebesgue measure, and $g_1,\dots,g_K$ are continuous, $\nu$-integrable and satisfy the regularity condition. Let $G : \mathbb R^K \to \mathbb R$, and consider the problem (9)–(12) of minimizing
--   $$G(A_1,\dots,A_K) + \sum_k \int_{\mathcal A_k} g_k\,d\nu, \qquad A_k = \nu(\mathcal A_k),$$
--   over partitions $(\mathcal A_1, \dots, \mathcal A_K)$ of $\mathcal S$.
--
--   Let $\bar{\mathcal A}$ be a local optimum (for some $\varepsilon > 0$, no partition $\mathcal A'$ with $\nu(\mathcal A'_k \triangle \bar{\mathcal A}_k) < \varepsilon$ for all $k$ is cheaper), with areas $\bar A$, and suppose $G$ is differentiable at $\bar A$. Then for every $k$, for $\nu$-almost every $x \in \bar{\mathcal A}_k$,
--   $$g_k(x) + \frac{\partial G(\bar A)}{\partial A_k} \le g_j(x) + \frac{\partial G(\bar A)}{\partial A_j} \qquad \text{for all } j \ne k.$$
--
--   The theorem identifies the Voronoi weights of a locally optimal partition with the gradient of $G$; it is the tool from which Theorem 5 (the socially optimal partition with optimized service rates) is derived.
--
--   **Formalization Note** The paper assumes the $g_k$ and $G$ differentiable everywhere. Theorem 5 applies the result to $g_k = d_k$ (not differentiable at $x_k$) and to $G = \frac{c}{B-\lambda}(\sum_k \sqrt{A_k})^2$ (not differentiable at a zero area), so the statement asks only for continuous, integrable $g_k$ and differentiability of $G$ at $\bar A$ — weaker hypotheses, hence a stronger statement. The conclusion holds $\nu$-almost everywhere on $\bar{\mathcal A}_k$, since local optima are only determined up to null sets. $\partial G(\bar A)/\partial A_k$ is the Fréchet derivative of $G$ at $\bar A$ applied to the $k$-th unit vector.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 14, Theorem 4; problem (9)–(12), p. 14; setting of §4.1, p. 13

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem theorem_4 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (g : Fin K → E n → ℝ)
    (G : (Fin K → ℝ) → ℝ) (hset : GeneralSetting S ν g) (A : Fin K → Set (E n))
    (hopt : IsLocalOptPartition ν S G g A) (hG : DifferentiableAt ℝ G (areas ν A)) :
    ∀ k, ∀ᵐ x ∂ν, x ∈ A k → ∀ j, j ≠ k →
      g k x + fderiv ℝ G (areas ν A) (Pi.single k (1 : ℝ)) ≤
        g j x + fderiv ℝ G (areas ν A) (Pi.single j (1 : ℝ)) := by sorry

end SpatialDemandEq.Optimal
