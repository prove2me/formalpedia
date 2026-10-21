-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_lemma_6
-- name    : SpatialDemandEq.Optimal.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:07.708374+00:00
-- url     : https://prove2.me/theorems/2dab9549-758e-4103-9aa0-e4f98ef5e855
-- title:
--   Lemma 6, p. 34 — an optimal partition with prescribed areas is a weighted Voronoi diagram {g_k − η_k ≤ g_j − η_j}
-- statement:
--   Work in the setting of §4.1: $\mathcal S \subseteq \mathbb R^n$ is closed and convex, $\nu$ is a probability measure on $\mathcal S$ that is absolutely continuous with respect to Lebesgue measure, and $g_1,\dots,g_K : \mathbb R^n \to \mathbb R$ are continuous, $\nu$-integrable and regular (for $j \ne k$ the law of $g_j(Y) - g_k(Y)$ under $Y \sim \nu$ has a density).
--
--   Let $\mathcal A'$ be a partition of $\mathcal S$ (measurable pieces, $\bigcup_k \mathcal A'_k = \mathcal S$, $\nu(\mathcal A'_j \cap \mathcal A'_k) = 0$ for $j \ne k$) with areas $A_k = \nu(\mathcal A'_k) > 0$, which is optimal for the inner problem (28): among all partitions $\mathcal A$ of $\mathcal S$ with $\nu(\mathcal A_k) = A_k$ for every $k$, it minimizes $\sum_k \int_{\mathcal A_k} g_k\,d\nu$. Then there are constants $\eta_1,\dots,\eta_K$ such that, for every $k$, up to a $\nu$-null set,
--   $$\mathcal A'_k = \{x \in \mathcal S : g_k(x) - \eta_k \le g_j(x) - \eta_j \text{ for all } j\}. \tag{29}$$
--
--   This is the inner layer of the decomposition (27) of the general partitioning problem: once the areas are fixed, the optimal partition is an additively weighted Voronoi diagram. It is the main step towards Theorem 4.
--
--   **Formalization Note** The identity (29) is stated up to $\nu$-null sets ($=^{\mathrm{ae}}_\nu$): a null modification of an optimal partition is still optimal, so the pointwise identity is false. The hypothesis that every prescribed area is positive is added; with a zero area and unbounded $g_j - g_k$ no finite $\eta$ need exist. Integrability of the $g_k$ is added so that (28) is a real number; differentiability of the $g_k$ is not assumed.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 34, §8.1, Lemma 6 (equations (28)–(29)); setting of §4.1, p. 13

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem lemma_6 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (g : Fin K → E n → ℝ)
    (hset : GeneralSetting S ν g) (A : Fin K → Set (E n)) (hA : IsPartition ν S A)
    (hpos : ∀ k, 0 < area ν (A k))
    (hmin : ∀ A' : Fin K → Set (E n), IsPartition ν S A' →
      (∀ k, area ν (A' k) = area ν (A k)) → linCost ν g A ≤ linCost ν g A') :
    ∃ η : Fin K → ℝ, ∀ k, A k =ᵐ[ν] {x | x ∈ S ∧ ∀ j, g k x - η k ≤ g j x - η j} := by sorry

end SpatialDemandEq.Optimal
