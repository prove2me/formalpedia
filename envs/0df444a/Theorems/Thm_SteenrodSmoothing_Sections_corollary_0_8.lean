-- Prove2me | Theorems.Thm_SteenrodSmoothing_Sections_corollary_0_8
-- name    : SteenrodSmoothing.Sections.corollary_0_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:24.24399+00:00
-- url     : https://prove2.me/theorems/d4b5b2d8-3584-42f5-aaa0-3adc1d124ff8
-- title:
--   Corollary 0.8, p. 3 — smooth maps into an open subset V of Y are dense in C(M, V) with the compact-open topology
-- statement:
--   Let $M$ be a finite-dimensional σ-compact Hausdorff manifold with corners, $Y$ a real normed space and $V \subseteq Y$ open. Then the smooth maps $M \to V$ are dense in the space $C(M, V)_{c.o.}$ of continuous maps $M \to V$ with the compact-open topology:
--   $$\overline{C^\infty(M, V)} = C(M, V)_{c.o.}.$$
--   Here a map $f : M \to V$ is smooth when $f$, viewed as a map into $Y$, is $C^\infty$.
--
--   The corollary is used in Lemma 0.9 to find a smooth map inside a prescribed compact-open neighbourhood with values in a convex open set.
--
--   **Formalization Note** The paper allows any locally convex space $Y$; here $Y$ is a real normed space. $C(M, V)$ is the space of continuous maps into the subtype $V$, with its compact-open topology, so neighbourhoods are taken in $C(M, V)$ and not in $C(M, Y)$. The model with corners may be any finite-dimensional Mathlib model with corners.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, p. 3, Corollary 0.8

import Mathlib

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

theorem corollary_0_8
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (V : Set Y) (hV : IsOpen V) :
    Dense {f : C(M, V) | ContMDiff I 𝓘(ℝ, Y) ∞ (fun x => (f x : Y))} := by sorry

end SteenrodSmoothing.Sections
