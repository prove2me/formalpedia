-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5
-- name    : PersistClust.Count.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:03.513012+00:00
-- url     : https://prove2.me/theorems/8476e8c8-3232-437b-939f-4ea37c366d80
-- title:
--   Theorem 4.5, p. 19 — a multi-bijection D₀f → D₀𝓡^f_δ(L) moves points by ≤ cδ in Q^NE_α and abscissae by ≤ cδ in Q^SE_α
-- statement:
--   Let $\mathbb X$ be a Riemannian manifold, possibly non-compact and possibly with boundary, whose strong convexity radius $\varrho_c(\mathbb X)$ is positive. Let $L\subseteq\mathbb X$ be a finite point cloud and $f:\mathbb X\to\mathbb R$ a tame $c$-Lipschitz function ($c\ge0$). Let $0<\delta<\varrho_c(\mathbb X)$ and $\alpha\in\mathbb R$ be such that $L$ is a geodesic $\delta/4$-sample of $\mathbb F^\alpha=f^{-1}([\alpha,\infty))$. Then there is a multi-bijection $\gamma$ between the $0$-th persistence diagram $D_0f$ of the superlevel-set filtration of $f$ and the $0$-th persistence diagram $D_0\mathcal R^f_\delta(L)$ of the upper-star Rips filtration, such that
--
--   1. $\forall p\in D_0f\cap Q^{NE}_\alpha$, $\|p-\gamma(p)\|_\infty\le c\delta$;
--   2. $\forall q\in D_0\mathcal R^f_\delta(L)\cap Q^{NE}_\alpha$, $\|\gamma^{-1}(q)-q\|_\infty\le c\delta$;
--   3. $\forall p\in D_0f\cap Q^{SE}_\alpha$, $|p_x-\gamma(p)_x|\le c\delta$;
--   4. $\forall q\in D_0\mathcal R^f_\delta(L)\cap Q^{SE}_\alpha$, $|\gamma^{-1}(q)_x-q_x|\le c\delta$.
--
--   It is the stability step of the main theorem: above the level $\alpha$ the diagram computed from the sample approximates the diagram of $f$.
--
--   **Formalization Note** A multi-bijection is a bijection between the copies of the points of the two diagrams, the diagonal contributing countably many copies of each of its points $(x,x)$, $x\in[-\infty,+\infty]$; the assertions quantify over all copies. On the Rips side the vertex set is $L$ itself, with the ambient (geodesic) distance and $g=f|_L$.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 19, Theorem 4.5

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem theorem_4_5
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4)) :
    ∃ γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ),
      SatisfiesIIV γ α (c * δ) := by sorry

end PersistClust.Count
