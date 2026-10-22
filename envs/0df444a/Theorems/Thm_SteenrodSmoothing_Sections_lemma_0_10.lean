-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_lemma_0_10
-- name    : SteenrodSmoothing.Sections.lemma_0_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:59.478216+00:00
-- url     : https://prove2.me/theorems/3ad822d8-f142-4b55-8bba-b78b063c822a
-- title:
--   Lemma 0.10, p. 4 — relative smoothing of a continuous map into a convex chart domain W ⊆ N, inside any compact-open neighbourhood
-- statement:
--   Let $M$ be a finite-dimensional σ-compact Hausdorff manifold with corners and $N$ a Hausdorff smooth manifold modelled on a real normed space $F$. Let $W \subseteq N$ be diffeomorphic to an open convex subset of $F$, and let $f : M \to W$ be continuous. Let $L \subseteq M$ be closed and $U \subseteq M$ open, and assume that $f$ is smooth on a neighbourhood of $L \setminus U$. Then every neighbourhood $\mathcal N$ of $f$ in $C(M, W)_{c.o.}$ contains a map $g : M \to W$ such that
--
--   1. $g$ is smooth on a neighbourhood of $L$, and
--   2. $$g(x) = f(x) \quad \text{for all } x \in M \setminus U .$$
--
--   This is Lemma 0.9 transported through a convex chart of $N$. In the proof of the generalised Steenrod approximation theorem it is applied, over one trivialising set at a time, to the fibre part of the section.
--
--   **Formalization Note** The paper allows $N$ to be modelled on any locally convex space; here its model is a real normed space $F$ (boundaryless; "Hausdorff" is part of the paper's definition of a locally convex manifold). "$W$ diffeomorphic to an open convex subset of $F$" is a $C^\infty$ partial diffeomorphism $N \to F$ with source $W$ and convex open target. The maps $f$, $g$ are elements of $C(M, W)$ (continuous maps into the subtype $W$, compact-open topology), and smoothness refers to the composite $M \to W \hookrightarrow N$. The model with corners of $M$ may be any finite-dimensional Mathlib model with corners.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 4, Lemma 0.10

import Mathlib
import Definitions.Def_SteenrodSmoothing_Sections_Setting

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem lemma_0_10
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]
    (W : Set N) (hW : IsConvexChartDomain F W) (f : C(M, W))
    (L U : Set M) (hL : IsClosed L) (hU : IsOpen U)
    (hf : SmoothNear I 𝓘(ℝ, F) (fun x => (f x : N)) (L \ U)) :
    ∀ 𝒩 ∈ 𝓝 f, ∃ g ∈ 𝒩,
      SmoothNear I 𝓘(ℝ, F) (fun x => (g x : N)) L ∧ ∀ x, x ∉ U → g x = f x := by sorry

end SteenrodSmoothing.Sections
