-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_hilbertMap_smooth_iff_kernel
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.hilbertMap_smooth_iff_kernel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:09:49.153633+00:00
-- url     : https://prove2.me/theorems/c91a662d-a0bf-4e64-8543-1282234afce9
-- title:
--   Hilbert-valued smoothness and the inner-product kernel
-- statement:
--   Let $M$ be a Hausdorff smooth manifold modeled on a real Hausdorff locally convex space, and let $H$ be a complete real or complex Hilbert space. For an arbitrary map $\gamma:M\to H$, set $K(x,y)=\langle\gamma(x),\gamma(y)\rangle$, using the source's inner product, linear in its first argument. Then
--
--   $$\gamma\text{ is smooth}\quad\Longleftrightarrow\quad K\text{ is smooth on }M\times M.$$
--
--   Smoothness means existence of all iterated real directional derivatives, jointly continuous in the base point and all directions in every chart. This criterion detects Hilbert-valued smoothness from a scalar kernel, without assuming continuity of $\gamma$ or any nondegeneracy.
--
--   **Formalization Note** The local definitions implement Definition 2.1 directly. The complex scalar is represented by Lean's inner product with its two arguments swapped.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 21, Theorem 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

/-- Theorem 7.1, PDF pp. 21–23: Hilbert-valued smoothness is equivalent
to smoothness of the inner-product kernel. Both real and complex Hilbert
spaces are allowed. The inner-product arguments are swapped to match the
source's linear-first scalar. No continuity of gamma is assumed. -/
theorem hilbertMap_smooth_iff_kernel
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E]
    {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    (hAtlas : BastianiAtlas (E := E) (M := M))
    {K : Type v} [RCLike K]
    {H : Type z} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
    (gamma : M → H) :
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ K H
    BastianiSmoothMap (E := E) gamma ↔
      BastianiSmoothKernel (E := E)
        (fun p : M × M => inner K (gamma p.2) (gamma p.1)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P22
