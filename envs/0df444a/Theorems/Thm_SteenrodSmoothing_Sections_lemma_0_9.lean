-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_lemma_0_9
-- name    : SteenrodSmoothing.Sections.lemma_0_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:03.218115+00:00
-- url     : https://prove2.me/theorems/50eb6ba7-4416-4c5e-9f61-e104e7e85971
-- title:
--   Lemma 0.9, p. 3 — relative smoothing of a continuous map into an open convex W ⊆ Y, inside any compact-open neighbourhood
-- statement:
--   Let $M$ be a finite-dimensional σ-compact Hausdorff manifold with corners, $Y$ a real normed space, $W \subseteq Y$ open and convex, and $f : M \to W$ continuous. Let $L \subseteq M$ be closed and $U \subseteq M$ open, and assume that $f$ is smooth on a neighbourhood of $L \setminus U$ (on some open set containing $L \setminus U$). Then every neighbourhood $\mathcal N$ of $f$ in $C(M, W)_{c.o.}$ contains a continuous map $g : M \to W$ such that
--
--   1. $g$ is smooth on a neighbourhood of $L$, and
--   2. $$g(x) = f(x) \quad \text{for all } x \in M \setminus U .$$
--
--   This relative smoothing lemma (after Hirsch, Theorem 2.5) is the local step of the proof of the generalised Steenrod approximation theorem: transported through a convex chart (Lemma 0.10) it smooths a section over one trivialising set without disturbing it outside a given open set.
--
--   **Formalization Note** The paper allows any locally convex space $Y$; here $Y$ is a real normed space. The map $f$ and the maps $g$ are elements of $C(M, W)$ (continuous maps into the subtype $W$, compact-open topology), and smoothness refers to the composite $M \to W \hookrightarrow Y$. "Smooth on a neighbourhood of a set" means $C^\infty$ on an open set containing it. The model with corners may be any finite-dimensional Mathlib model with corners.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 3, Lemma 0.9

import Mathlib
import Definitions.Def_SteenrodSmoothing_Sections_Setting

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem lemma_0_9
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (W : Set Y) (hWo : IsOpen W) (hWc : Convex ℝ W) (f : C(M, W))
    (L U : Set M) (hL : IsClosed L) (hU : IsOpen U)
    (hf : SmoothNear I 𝓘(ℝ, Y) (fun x => (f x : Y)) (L \ U)) :
    ∀ 𝒩 ∈ 𝓝 f, ∃ g ∈ 𝒩,
      SmoothNear I 𝓘(ℝ, Y) (fun x => (g x : Y)) L ∧ ∀ x, x ∉ U → g x = f x := by sorry

end SteenrodSmoothing.Sections
