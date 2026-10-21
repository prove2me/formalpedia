-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P15_remark_I_3_9
-- name    : QAlgorithms.Papers.Independent.Next46.P15.remark_I_3_9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:17:22.975961+00:00
-- url     : https://prove2.me/theorems/79f6b54f-a5f8-45d3-a8b9-4ba5d5796e1a
-- title:
--   A local diffeomorphism with discontinuous cotangent pullback
-- statement:
--   Let $E$ be a Hausdorff real locally convex space whose topology is not induced by a norm, and let $0\ne\alpha\in E'$ be continuous and linear. Define
--   $$f(x)=(1+\alpha(x))x,\qquad \phi(s)=\frac{\sqrt{1+4s}-1}{2}.$$
--   The map $f$ is smooth and
--   $$df(x)v=(1+\alpha(x))v+\alpha(v)x.$$
--   This differential is invertible whenever $\alpha(x)\notin\{-1,-\tfrac12\}$. On the open zero-neighborhoods $U=\{x:\alpha(x)>-\tfrac12\}$ and $V=\{y:\alpha(y)>-\tfrac14\}$, $f$ is a smooth diffeomorphism with inverse
--   $$f^{-1}(y)=\bigl(1+\phi(\alpha(y))\bigr)^{-1}y.$$
--   Its covector pullback satisfies
--   $$\lambda\circ df(x)=(1+\alpha(x))\lambda+\lambda(x)\alpha.$$
--   For every Hausdorff vector topology on $E'$, the resulting map $U\times E'\to E'$ is discontinuous.
--
--   This is the explicit obstruction to a natural cotangent vector-bundle structure in this example. Hausdorffness of the dual vector topology is the paper's standing convention; the indiscrete topology is excluded.
-- source:
--   Towards a Lie theory for locally convex groups, arXiv:1501.06269v1, PDF p. 17, Remark I.3.9 (explicit unnumbered result)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

open scoped BigOperators

universe u v w z

/-- Remark I.3.9, PDF p.17: the explicit smooth polynomial local
diffeomorphism, its inverse branch, differential, and discontinuous covector
pullback for every Hausdorff vector topology on the dual. -/
theorem remark_I_3_9
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    (hNonNormable : ¬ IsNormableLC E)
    (alpha : E →L[ℝ] ℝ) (hAlpha : alpha ≠ 0) :
    let U : Set E := {x | -(1 / 2 : ℝ) < alpha x}
    let V : Set E := {y | -(1 / 4 : ℝ) < alpha y}
    IsMBSmoothOn Set.univ (cotangentExample alpha) ∧
    (∀ x v : E, directionalDerivative (cotangentExample alpha) x v =
      (1 + alpha x) • v + alpha v • x) ∧
    (∀ x : E, alpha x ≠ -1 → alpha x ≠ -(1 / 2 : ℝ) →
      ∃ A : E ≃L[ℝ] E, ∀ v : E,
        A v = directionalDerivative (cotangentExample alpha) x v) ∧
    (IsOpen U ∧ (0 : E) ∈ U ∧ IsOpen V ∧ (0 : E) ∈ V ∧
      Set.MapsTo (cotangentExample alpha) U V ∧
      Set.MapsTo (cotangentExampleInverse alpha) V U ∧
      (∀ x ∈ U, cotangentExampleInverse alpha (cotangentExample alpha x) = x) ∧
      (∀ y ∈ V, cotangentExample alpha (cotangentExampleInverse alpha y) = y) ∧
      IsMBSmoothOn V (cotangentExampleInverse alpha)) ∧
    (∀ (x : E) (ell : E →L[ℝ] ℝ) (v : E),
      cotangentExamplePullback alpha x ell v =
        ell (directionalDerivative (cotangentExample alpha) x v)) ∧
    (∀ tau : TopologicalSpace (E →L[ℝ] ℝ),
      letI : TopologicalSpace (E →L[ℝ] ℝ) := tau
      IsTopologicalAddGroup (E →L[ℝ] ℝ) → ContinuousSMul ℝ (E →L[ℝ] ℝ) →
        T2Space (E →L[ℝ] ℝ) →
        ¬ Continuous (fun p : U × (E →L[ℝ] ℝ) =>
          cotangentExamplePullback alpha p.1.val p.2)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P15

end
